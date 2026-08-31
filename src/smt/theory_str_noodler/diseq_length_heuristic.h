#ifndef _NOODLER_DISEQ_LENGTH_HEURISTIC_H_
#define _NOODLER_DISEQ_LENGTH_HEURISTIC_H_

#include <map>
#include <optional>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "decision_procedure.h"
#include "formula_preprocess.h"
#include "formula.h"
#include "util.h"

namespace smt::noodler {

    class DiseqLengthModelHandler {
    private:
        AutAssignment aut_ass{};
        SubstitutionMap subst_map{};
        std::map<BasicTerm, zstring> model{};

        /**
         * @brief Pick a word for a variable @p var in aut_ass of the exact length (if needed) given in @p arith_model using its automaton.
         */
        zstring assign_aut_ass_var(const BasicTerm& var, const std::map<BasicTerm, rational>& arith_model) {
            SASSERT(var.is_variable());
            mata::Word resulting_word;
            if (arith_model.contains(var)) { // var might not be length sensitive (if it only occurs in regex and was not intially length sensitive)
                const rational& total_length = arith_model.at(var);
                if (!total_length.is_int32()) { util::throw_error(std::string("Length of ") + var.to_string() + std::string(" is too large for mata to handle")); }
                mata::nfa::Nfa sigma_length = this->aut_ass.sigma_automaton_of_length(total_length.get_int32());
                resulting_word = mata::nfa::intersection(sigma_length, *this->aut_ass.at(var)).get_word().value(); // will throw exception if aut_ass is empty (should not happen)
            } else {
                resulting_word = this->aut_ass.at(var)->get_word().value();
            }
            zstring res = aut_ass.get_alphabet().get_string_from_mata_word(resulting_word);
            model[var] = res;
            return res;
        }

        /**
         * @brief Expand a substitution-map variable by recursively resolving concats.
         */
        zstring assign_subst_map_var(const BasicTerm& var, const std::map<BasicTerm, rational>& arith_model) {
            const Concat& subst = this->subst_map.at(var);
            zstring res = "";
            for (const BasicTerm& term : subst) {
                res = res + get_model(term, arith_model);
            }
            model[var] = res;
            return res;
        }

    public:
        /**
         * @brief Default construction.
         */
        DiseqLengthModelHandler() = default;
        /**
         * @brief Construct with initial automata and substitution map.
         */
        DiseqLengthModelHandler(AutAssignment aut, SubstitutionMap subst)
            : aut_ass(std::move(aut)), subst_map(std::move(subst)) {}

        /**
         * @brief Refresh stored data and drop cached models.
         */
        void update_data(AutAssignment aut, SubstitutionMap subst) {
            this->aut_ass = std::move(aut);
            this->subst_map = std::move(subst);
            this->model.clear();
        }

        /**
         * @brief Return the cached model for @p var, computing the cache if needed.
         */
        zstring get_model(const BasicTerm& var, const std::map<BasicTerm, rational>& arith_model) {
            if(var.is_literal()) {
                return var.get_name();
            } else if (model.contains(var)) {
                return model.at(var);
            } else if (subst_map.contains(var)) {
                return assign_subst_map_var(var, arith_model);
            } else {
                SASSERT(aut_ass.contains(var));
                return assign_aut_ass_var(var, arith_model);
            }
        }
    };

    /**
     * @brief Heuristic decision procedure for instances containing only word disequations
     * (and possibly regex memberships handled elsewhere). It builds a length-only
     * constraint requiring each disequation to have different lengths.
     */
    class DiseqLengthHeuristicProcedure : public AbstractDecisionProcedure {
        Formula diseq_formula;
        AutAssignment aut_ass;
        std::unordered_set<BasicTerm> length_sensitive_vars;
        const theory_str_noodler_params& m_params;
        SubstitutionMap subst_map{};
        DiseqLengthModelHandler model_handler{};

        // the length formula from preprocessing, get_lengths should create conjunct with it
        LenNode preprocessing_len_formula = LenNode(LenFormulaType::TRUE,{});

    public:
        /**
         * Initialize the disequation-length heuristic for formulas containing only disequations.
         *
         * @param diseq_formula Formula containing only disequations
         * @param aut_ass Automaton assignment for variables in the formula
         * @param params Parameters for Noodler string theory
         */
        DiseqLengthHeuristicProcedure(Formula diseq_formula, AutAssignment aut_ass, std::unordered_set<BasicTerm> init_length_sensitive_vars, const theory_str_noodler_params& params)
            : diseq_formula(std::move(diseq_formula)), aut_ass(std::move(aut_ass)), length_sensitive_vars(std::move(init_length_sensitive_vars)), m_params(params) {
            auto vars = this->diseq_formula.get_vars();
            this->length_sensitive_vars.insert(vars.begin(), vars.end());
            model_handler.update_data(this->aut_ass, this->subst_map);
        }

        /**
         * Do lightweight preprocessing: propagate eps/variables, drop trivial constraints, refresh state, and detect trivial UNSAT.
         *
         * @param opt Preprocess option (ignored)
         * @param len_eq_vars Equivalence classes of variables with equal length (ignored)
         * @return lbool representing whether preprocessing solved the formula
         */
        lbool preprocess(PreprocessType, const BasicTermEqiv&) override {
            FormulaPreprocessor prep_handler(this->diseq_formula, this->aut_ass, this->length_sensitive_vars, m_params, {});

            // these rules are useful only for equations, but we can have some in diseq_formula, as suitability check runs them too to see if they are all removed
            prep_handler.propagate_eps();
            prep_handler.propagate_variables();
            prep_handler.remove_trivial();

            this->diseq_formula = prep_handler.get_modified_formula();
            this->aut_ass = prep_handler.get_aut_assignment();
            this->length_sensitive_vars = prep_handler.get_len_variables();
            this->preprocessing_len_formula = prep_handler.get_len_formula();
            this->subst_map = prep_handler.get_substitution_map();
            
            if (this->diseq_formula.get_predicates().size() > 0) {
                this->aut_ass.reduce();
            }

            this->model_handler.update_data(this->aut_ass, this->subst_map);

            if (prep_handler.contains_unsat_eqs_or_diseqs()) {
                return l_false;
            }
            if(!this->aut_ass.is_sat()) {
                return l_false;
            }

            return l_undef;
        }

        /**
         * Initialize the computation (no-op, heuristic is single-shot).
         */
        void init_computation() override {}

        /**
         * Compute next solution (returns l_false because the heuristic has no worklist).
         */
        lbool compute_next_solution() override { return l_false; }

        /**
         * Get initial length constraints (only true for this heuristic).
         */
        LenNode get_initial_lengths(bool) override { return LenNode(LenFormulaType::TRUE); }

        /**
         * Get length constraints ensuring each disequation has different lengths.
         *
         * @return Pair of length node and precision (always precise)
         */
        std::pair<LenNode, LenNodePrecision> get_lengths() override {
            std::vector<LenNode> conjuncts;
            conjuncts.emplace_back(this->preprocessing_len_formula);

            for (const auto& t : this->aut_ass) {
                BasicTerm term = t.first;
                conjuncts.emplace_back(LenFormulaType::LEQ, std::vector<LenNode>{LenNode(0), LenNode(term)});
                conjuncts.emplace_back(this->aut_ass.get_lengths(term));
            }
            for (const auto& diseq : diseq_formula.get_predicates()) {
                conjuncts.push_back(diseq.get_formula_eq()); // produces |lhs| != |rhs|
            }
            return {LenNode(LenFormulaType::AND, std::move(conjuncts)), LenNodePrecision::UNDERAPPROX};
        }

        /**
         * Get variables whose lengths may influence the model of any string variable.
         *
         * @param str_var String variable for which the model is requested
         * @return Vector of variables affecting length constraints
         */
        std::vector<BasicTerm> get_len_vars_for_model(const BasicTerm& var) override {
            return std::vector<BasicTerm>(length_sensitive_vars.begin(), length_sensitive_vars.end());
        }

        /**
         * Get string model for the variable @p var using the arithmetic model.
         *
         * @param var String variable whose model is requested
         * @param arith_model Maps variables to their lengths in the arithmetic model
         * @return Word of the requested length accepted by the automaton, empty string on failure
         */
        zstring get_model(BasicTerm var, const std::map<BasicTerm, rational>& arith_model) override {
            return this->model_handler.get_model(var, arith_model);
        }

        /**
         * Check whether the instance is suitable for this heuristic (contains only disequations).
         *
         * @param instance Formula to check
         * @param aut_assignment Automaton assignment of the formula
         * @return True iff the instance contains only disequations after preprocessing
         */
        static bool is_suitable(const Formula& instance, const AutAssignment& aut_assignment) {
            // these simple preprocessing rules to remove equations will be used in preprocess(), so it might be helpful to check if they leave us only with disequations
            theory_str_noodler_params params;
            FormulaPreprocessor prep_handler(instance, aut_assignment, {}, params, {});
            prep_handler.propagate_eps();
            prep_handler.propagate_variables();
            prep_handler.remove_trivial();

            const Formula& pre_f = prep_handler.get_modified_formula();

            if (pre_f.contains_pred_type(PredicateType::Equation)
                || pre_f.contains_pred_type(PredicateType::Transducer)
                || pre_f.contains_pred_type(PredicateType::NotContains)
                || !pre_f.contains_pred_type(PredicateType::Inequation)
                || !prep_handler.get_removed_inclusions_for_model().empty()) // the used preprocessing rules should not add anything to removed_inclusions_for_model, but just to be safe
            {
                return false;
            }

            return true;
        }

    };
}

#endif
