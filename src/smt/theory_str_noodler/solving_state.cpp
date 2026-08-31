#include "solving_state.h"
#include "formula_preprocess.h"
#include "inclusion_graph.h"

#include <limits>

namespace smt::noodler {



    bool SolvingState::substitute_vars(const std::set<BasicTerm>& vars_to_substitute) {
        // Build substitution map restricted to the variables actually being substituted.
        std::unordered_map<BasicTerm, std::vector<BasicTerm>> cur_subst;
        for (const BasicTerm& v : vars_to_substitute) {
            auto it = substitution_map.find(v);
            if (it != substitution_map.end())
                cur_subst[v] = it->second;
        }

        // returns true if the inclusion has the same thing on both sides
        auto inclusion_has_same_sides = [](const Predicate &inclusion) { return (inclusion.is_equation() && inclusion.get_left_side() == inclusion.get_right_side()); };

        const std::set<Predicate> old_predicates_not_on_cycle = predicates_not_on_cycle;
        const std::map<Predicate, size_t> old_inclusion_depths = inclusion_depths;

        // Derived empty-side equations inherit the generation of their source.
        std::map<Predicate, size_t> derived_inclusions;
        auto collect_simplification_result = [&derived_inclusions](
                Predicate::EquationSimplificationResult& result, size_t source_depth) -> bool {
            if (result.kind == Predicate::EquationSimplificationResult::Kind::Infeasible) {
                return false;
            }
            if (result.kind == Predicate::EquationSimplificationResult::Kind::EmptySideConsequence) {
                Predicate derived = Predicate::create_equation(std::move(result.residual), {});
                const size_t derived_depth = std::max<size_t>(1, source_depth);
                auto [it, inserted] = derived_inclusions.emplace(std::move(derived), derived_depth);
                if (!inserted) it->second = std::min(it->second, derived_depth);
            }
            return true;
        };

        std::set<Predicate> new_inclusions;
        std::set<Predicate> new_transducers;
        std::set<Predicate> new_predicates_not_on_cycle;
        std::map<Predicate, size_t> new_inclusion_depths;
        auto insert_simplified_inclusion = [&](Predicate predicate, bool on_cycle, size_t source_depth) {
            if (inclusion_has_same_sides(predicate)) return;
            new_inclusions.insert(predicate);
            if (!on_cycle) {
                new_predicates_not_on_cycle.insert(std::move(predicate));
            } else {
                auto [it, inserted] = new_inclusion_depths.emplace(std::move(predicate), source_depth);
                if (!inserted) it->second = std::min(it->second, source_depth);
            }
        };

        for (const Predicate& old_pred : inclusions) {
            const bool on_cycle = !old_predicates_not_on_cycle.contains(old_pred);
            size_t source_depth = 0;
            if (on_cycle) {
                SASSERT(old_inclusion_depths.contains(old_pred));
                source_depth = old_inclusion_depths.at(old_pred);
            }
            Predicate new_pred = old_pred;
            Predicate::EquationSimplificationResult result = new_pred.apply_subst(cur_subst);
            if (!collect_simplification_result(result, source_depth)) {
                return false;
            }
            insert_simplified_inclusion(std::move(new_pred), on_cycle, source_depth);
            for (auto& split : result.split_equations) {
                insert_simplified_inclusion(
                    Predicate::create_equation(std::move(split.left), std::move(split.right)),
                    on_cycle,
                    source_depth);
            }
        }

        for (const Predicate& old_pred : transducers) {
            Predicate new_pred = old_pred;
            Predicate::EquationSimplificationResult result = new_pred.apply_subst(cur_subst);
            if (!collect_simplification_result(result, 0)) return false;
            SASSERT(result.split_equations.empty());
            new_transducers.insert(new_pred);
            if (old_predicates_not_on_cycle.contains(old_pred)) {
                new_predicates_not_on_cycle.insert(new_pred);
            }
        }

        // If differently classified sources collapse to one predicate, retain the
        // conservative not-on-cycle classification used by the previous code.
        for (const Predicate& predicate : new_predicates_not_on_cycle) {
            new_inclusion_depths.erase(predicate);
        }

        inclusions = std::move(new_inclusions);
        transducers = std::move(new_transducers);
        predicates_not_on_cycle = std::move(new_predicates_not_on_cycle);
        inclusion_depths = std::move(new_inclusion_depths);

        // substituting predicates to process is bit harder, it is possible that two predicates that were supposed to
        // be processed become same after substituting, so we do not want to keep both in predicates to process
        PredicateQueue new_predicates_to_process{
            predicates_to_process.heuristic_enabled()};
        while (!predicates_to_process.empty()) {
            bool cur_p = predicates_to_process.top_priority();
            std::optional<size_t> source_depth = predicates_to_process.top_depth();
            Predicate substituted_inclusion = predicates_to_process.top();
            if (!source_depth.has_value()) {
                auto depth_it = old_inclusion_depths.find(substituted_inclusion);
                if (depth_it != old_inclusion_depths.end()) source_depth = depth_it->second;
            }
            Predicate::EquationSimplificationResult result = substituted_inclusion.apply_subst(cur_subst);
            if (!collect_simplification_result(result, source_depth.value_or(0))) {
                return false;
            }
            predicates_to_process.pop();

            std::vector<Predicate> simplified_inclusions;
            simplified_inclusions.push_back(std::move(substituted_inclusion));
            for (auto& split : result.split_equations) {
                simplified_inclusions.push_back(
                    Predicate::create_equation(std::move(split.left), std::move(split.right)));
            }
            for (Predicate& simplified : simplified_inclusions) {
                if (inclusion_has_same_sides(simplified)) continue;
                std::optional<size_t> substituted_depth;
                auto depth_it = inclusion_depths.find(simplified);
                if (depth_it != inclusion_depths.end()) substituted_depth = depth_it->second;
                new_predicates_to_process.push(std::move(simplified), cur_p, substituted_depth);
            }
        }
        predicates_to_process = new_predicates_to_process;

        for (const auto& [derived, depth] : derived_inclusions) {
            // The derived equation is a safe consequence, but its graph position is unknown.
            // Treat it as on-cycle and give its empty-side processing high priority.
            add_predicate(derived, true, depth);
            enqueue_predicate(derived, true);
        }

        for (const Predicate& inclusion : inclusions) {
            SASSERT(predicates_not_on_cycle.contains(inclusion)
                    || inclusion_depths.contains(inclusion));
        }

        apply_substitutions_to_disequations();
        return true;
    }

    LenNode SolvingState::get_disequations_underapprox_length_formula() const {
        LenNode result{LenFormulaType::AND};
        for(const Predicate& diseq : postponed_disequations.get_predicates()) {
            result.succ.push_back(diseq.get_formula_eq());
        }
        return result;
    }

    std::set<BasicTerm> SolvingState::get_vars_referenced_by_state_constraints() const {
        std::set<BasicTerm> referenced_vars;

        for (const TermConversion& conversion : conversions) {
            referenced_vars.insert(conversion.string_var);
            referenced_vars.insert(conversion.number_var);
        }

        const std::set<BasicTerm> diseq_vars = postponed_disequations.get_vars();
        referenced_vars.insert(diseq_vars.begin(), diseq_vars.end());

        for (const LenNode& conjunct : disequations_len_formula_conjuncts) {
            const std::set<BasicTerm> vars_in_conjunct = collect_free_vars(conjunct);
            referenced_vars.insert(vars_in_conjunct.begin(), vars_in_conjunct.end());
        }

        return referenced_vars;
    }

    void SolvingState::mark_length_sensitive(const std::vector<BasicTerm>& terms) {
        std::set<BasicTerm> newly_marked;
        std::set<BasicTerm> visited;
        std::function<void(const BasicTerm&)> mark = [&](const BasicTerm& term) {
            if (!term.is_variable() || !visited.insert(term).second) return;
            if (length_sensitive_vars.insert(term).second) newly_marked.insert(term);
            auto it = substitution_map.find(term);
            if (it != substitution_map.end()) {
                for (const BasicTerm& replacement_term : it->second) mark(replacement_term);
            }
        };
        for (const BasicTerm& term : terms) mark(term);

        if (newly_marked.empty()) return;
        for (const Predicate& inclusion : inclusions) {
            if (is_dependent(newly_marked, inclusion.get_right_set())) {
                enqueue_predicate(inclusion, !is_predicate_on_cycle(inclusion));
            }
        }
        for (const Predicate& transducer : transducers) {
            if (is_dependent(newly_marked, transducer.get_set_of_param(0))) {
                enqueue_predicate(transducer, !is_predicate_on_cycle(transducer));
            }
        }
    }

    void SolvingState::apply_substitutions_to_disequations() {
        auto substitute_concat = [this](const std::vector<BasicTerm>& con) {
            std::vector<BasicTerm> result;
            for (const BasicTerm& bt : con) {
                const std::vector<BasicTerm> subst = get_substituted_vars(bt);
                result.insert(result.end(), subst.begin(), subst.end());
            }
            return result;
        };

        for (Predicate& diseq : postponed_disequations.get_predicates()) {
            SASSERT(diseq.is_inequation());
            diseq = Predicate::create_disequation(
                substitute_concat(diseq.get_left_side()),
                substitute_concat(diseq.get_right_side())
            );
        }
    }

    /**
     * Replace disequality @p diseq L != P by equalities L = x1a1y1 and R = x2a2y2
     * where x1,x2,y1,y2 \in \Sigma* and a1,a2 \in \Sigma \cup {\epsilon} and
     * also create arithmetic formula:
     *   |x1| = |x2| && to_code(a1) != to_code(a2) && (|a1| = 0 => |y1| = 0) && (|a2| = 0 => |y2| = 0)
     * The variables a1/a2 represent the characters on which the two sides differ
     * (they have different code values). They have to occur on the same position,
     * i.e. lengths of x1 and x2 are equal. The situation where one of the a1/a2
     * is empty word (to_code returns -1) represents that one of the sides is
     * longer than the other (they differ on the character just after the last
     * character of the shorter side). We have to force that nothing is after
     * the empty a1/a2, i.e. length of y1/y2 must be 0.
     */
    std::vector<Predicate> SolvingState::replace_disequality(const Predicate& diseq) {
        // automaton accepting empty word or exactly one symbol
        std::shared_ptr<mata::nfa::Nfa> sigma_eps_automaton = std::make_shared<mata::nfa::Nfa>(aut_ass.sigma_eps_automaton());

        // function that will take a1 and a2 and create the "to_code(a1) != to_code(a2)" part of the arithmetic formula
        auto create_to_code_ineq = [this](const BasicTerm& var1, const BasicTerm& var2) {
            // we are going to check that to_code(var1) != to_code(var2), we need exact languages, so we make them length
            length_sensitive_vars.insert(var1);
            length_sensitive_vars.insert(var2);

            // variables that are results of to_code applied to var1/var2
            BasicTerm var1_to_code = util::mk_internal_noodler_var(var1.get_name() + zstring("!ineq_to_code"));
            BasicTerm var2_to_code = util::mk_internal_noodler_var(var2.get_name() + zstring("!ineq_to_code"));

            // add the information that we need to process "var1_to_code = to_code(var1)" and "var2_to_code = to_code(var2)"
            conversions.push_back(TermConversion{ConversionType::TO_CODE, var1, var1_to_code});
            conversions.push_back(TermConversion{ConversionType::TO_CODE, var2, var2_to_code});

            // add to_code(var1) != to_code(var2) to the len formula for disequations
            disequations_len_formula_conjuncts.push_back(LenNode(LenFormulaType::NEQ, {var1_to_code, var2_to_code}));
        };

        // This optimization represents the situation where L = a1 and R = a2
        // and we know that a1,a2 \in \Sigma \cup {\epsilon}, i.e. we do not create new equations.
        if (diseq.get_left_side().size() == 1 && diseq.get_right_side().size() == 1) {
            BasicTerm a1 = diseq.get_left_side()[0];
            BasicTerm a2 = diseq.get_right_side()[0];
            auto autl = aut_ass.at(a1);
            auto autr = aut_ass.at(a2);

            if (mata::nfa::is_included(*autl, *sigma_eps_automaton) && mata::nfa::is_included(*autr, *sigma_eps_automaton)) {
                // create to_code(a1) != to_code(a2)
                create_to_code_ineq(a1, a2);
                STRACE(str_dis, tout << "from disequation " << diseq << " no new equations were created" << std::endl;);
                return std::vector<Predicate>();
            }
        }

        // automaton accepting everything
        std::shared_ptr<mata::nfa::Nfa> sigma_star_automaton = std::make_shared<mata::nfa::Nfa>(aut_ass.sigma_star_automaton());

        BasicTerm x1 = util::mk_noodler_var_fresh("diseq_start");
        aut_ass[x1] = sigma_star_automaton;
        BasicTerm a1 = util::mk_noodler_var_fresh("diseq_char");
        aut_ass[a1] = sigma_eps_automaton;
        BasicTerm y1 = util::mk_noodler_var_fresh("diseq_end");
        aut_ass[y1] = sigma_star_automaton;
        BasicTerm x2 = util::mk_noodler_var_fresh("diseq_start");
        aut_ass[x2] = sigma_star_automaton;
        BasicTerm a2 = util::mk_noodler_var_fresh("diseq_char");
        aut_ass[a2] = sigma_eps_automaton;
        BasicTerm y2 = util::mk_noodler_var_fresh("diseq_end");
        aut_ass[y2] = sigma_star_automaton;

        std::vector<Predicate> new_eqs;
        // L = x1a1y1
        new_eqs.push_back(Predicate::create_equation(diseq.get_left_side(), std::vector<BasicTerm>{x1, a1, y1}));
        // R = x2a2y2
        new_eqs.push_back(Predicate::create_equation(diseq.get_right_side(), std::vector<BasicTerm>{x2, a2, y2}));

        // we want |x1| == |x2|, making x1 and x2 length ones
        length_sensitive_vars.insert(x1);
        length_sensitive_vars.insert(x2);
        // |x1| = |x2|
        disequations_len_formula_conjuncts.push_back(LenNode(LenFormulaType::EQ, {x1, x2}));

        // create to_code(a1) != to_code(a2)
        create_to_code_ineq(a1, a2);

        // we are also going to check for the lengths of y1 and y2, so they have to be length
        length_sensitive_vars.insert(y1);
        length_sensitive_vars.insert(y2);
        // (|a1| = 0) => (|y1| = 0)
        disequations_len_formula_conjuncts.push_back(LenNode(LenFormulaType::OR, {LenNode(LenFormulaType::NEQ, {a1, 0}), LenNode(LenFormulaType::EQ, {y1, 0})}));
        // (|a2| = 0) => (|y2| = 0)
        disequations_len_formula_conjuncts.push_back(LenNode(LenFormulaType::OR, {LenNode(LenFormulaType::NEQ, {a2, 0}), LenNode(LenFormulaType::EQ, {y2, 0})}));

        STRACE(str_dis, tout << "from disequation " << diseq << " created equations: " << new_eqs[0] << " and " << new_eqs[1] << std::endl;);
        return new_eqs;
    }

    void SolvingState::translate_postponed_disequations_to_equations() {
        // we can add equations from replacing disequations as they are. The right side of 
        // each equation contains fresh variables only. Therefore, they cannot depend on 
        // alredy processed equations.
        for (const Predicate& diseq : postponed_disequations.get_predicates()) {
            for (const Predicate& eq_from_diseq : replace_disequality(diseq)) {
                add_predicate(eq_from_diseq, false);
                enqueue_predicate(eq_from_diseq, false);
            }
        }

        postponed_disequations.get_predicates().clear();
    }

    lbool SolvingState::preprocess_disequations_for_unsat(const theory_str_noodler_params& params) {
        if (postponed_disequations.get_predicates().empty()) {
            return l_true;
        }

        std::set<BasicTerm> conversion_vars;
        for (const TermConversion& conv : conversions) {
            conversion_vars.insert(conv.string_var);
        }

        FormulaPreprocessor prep_handler{postponed_disequations, aut_ass, length_sensitive_vars, params, conversion_vars};

        prep_handler.remove_trivial();
        prep_handler.reduce_diseqalities();
        prep_handler.propagate_eps();
        prep_handler.refine_languages();
        prep_handler.reduce_diseqalities();

        if (!prep_handler.get_aut_assignment().is_sat() || prep_handler.contains_unsat_eqs_or_diseqs()) {
            return l_false;
        }

        // Persist the simplified disequations and refined state back.
        postponed_disequations = prep_handler.get_modified_formula();
        aut_ass = prep_handler.get_aut_assignment();
        const std::unordered_set<BasicTerm>& prep_len_vars = prep_handler.get_len_variables();
        length_sensitive_vars.insert(prep_len_vars.begin(), prep_len_vars.end());

        return l_true;
    }

    void SolvingState::remove_vars(const std::set<BasicTerm>& vars_to_remove, const std::set<BasicTerm>& vars_to_keep) {
        std::set<BasicTerm> vars_required_by_state = get_vars_referenced_by_state_constraints();

        for (const BasicTerm& var : vars_to_remove) {
            if (vars_to_keep.contains(var)) {
                continue;
            }

            if (vars_required_by_state.contains(var)) {
                // Keep substitution/length information for variables that still occur in
                // state-local constraints (e.g., disequality replacement artifacts),
                // but remove direct automaton assignment to preserve substitution semantics.
                aut_ass.erase(var);
                continue;
            }

            substitution_map.erase(var);
            length_sensitive_vars.erase(var);
            aut_ass.erase(var);
        }
    }

    LenNode SolvingState::get_lengths(const BasicTerm& var) const {
        if (aut_ass.count(var) > 0) {
            // if var is not substituted, get length constraint from its automaton
            return aut_ass.get_lengths(var);
        } else if (substitution_map.count(var) > 0) {
            // if var is substituted, i.e. state.substitution_map[var] = x_1 x_2 ... x_n, then we have to create length equation
            //      |var| = |x_1| + |x_2| + ... + |x_n|
            std::vector<LenNode> plus_operands;
            for (const auto& subst_var : substitution_map.at(var)) {
                plus_operands.emplace_back(subst_var);
            }
            LenNode result(LenFormulaType::EQ, {var, LenNode(LenFormulaType::PLUS, plus_operands)});
            // to be safe, we add |var| >= 0 (for the aut_ass case, it is done in aut_ass.get_lengths)
            return LenNode(LenFormulaType::AND, {result, LenNode(LenFormulaType::LEQ, {0, var})});
        } else {
            util::throw_error("Variable was neither in automata assignment nor was substituted");
            return LenNode(BasicTerm(BasicTermType::Literal)); // return something to get rid of warnings
        }
    }

    void SolvingState::flatten_substition_map() {
        std::unordered_map<BasicTerm, std::vector<BasicTerm>> new_substitution_map;
        std::function<std::vector<BasicTerm>(const BasicTerm&)> flatten_var;

        flatten_var = [&new_substitution_map, &flatten_var, this](const BasicTerm &var) -> std::vector<BasicTerm> {
            if (new_substitution_map.count(var) == 0) {
                std::vector<BasicTerm> flattened_mapping;
                for (const auto &subst_var : this->substitution_map.at(var)) {
                    if (subst_var.is_literal() || aut_ass.count(subst_var) > 0) {
                        // subst_var is not substituted, keep it
                        flattened_mapping.push_back(subst_var);
                    } else {
                        // subst_var has a substitution, flatten it and insert it to the end of flattened_mapping
                        std::vector<BasicTerm> flattened_mapping_of_subst_var = flatten_var(subst_var);
                        flattened_mapping.insert(flattened_mapping.end(),
                                                 flattened_mapping_of_subst_var.begin(),
                                                 flattened_mapping_of_subst_var.end());
                    }
                }
                new_substitution_map[var] = flattened_mapping;
                return flattened_mapping;
            } else {
                return new_substitution_map[var];
            }
        };

        for (const auto &subst_map_pair : substitution_map) {
            flatten_var(subst_map_pair.first);
        }

        STRACE(str_nfa,
            tout << "Flattened substitution map:" << std::endl;
            for (const auto &var_map : new_substitution_map) {
                tout << "    " << var_map.first.get_name() << " ->";
                for (const auto &subst_var : var_map.second) {
                    tout << " " << subst_var;
                }
                tout << std::endl;
            });

        substitution_map = new_substitution_map;
        apply_substitutions_to_disequations();
    }

    std::pair<std::vector<std::shared_ptr<mata::nfa::Nfa>>,std::vector<std::vector<BasicTerm>>> SolvingState::get_automata_and_division_of_concatenation(const std::vector<BasicTerm>& concatenation, bool group_non_length) {
        if (concatenation.empty()) {
            return std::make_pair<std::vector<std::shared_ptr<mata::nfa::Nfa>>,std::vector<std::vector<BasicTerm>>>({}, {});
        }

        std::vector<std::shared_ptr<mata::nfa::Nfa>> automata_for_concatenation;
        std::vector<std::vector<BasicTerm>> divisions;

        auto requires_own_division = [&](const BasicTerm& v) -> bool {
            if (length_sensitive_vars.contains(v) || !v.is_variable()) return true;

            const Predicate* first_inclusion = nullptr;
            for (const Predicate& inclusion : inclusions) {
                if (std::count(inclusion.get_right_side().begin(),
                               inclusion.get_right_side().end(), v) >= 2) {
                    return true;
                }
                const bool occurs_on_left = inclusion.get_left_set().contains(v);
                const bool occurs_on_right = inclusion.get_right_set().contains(v);
                if (occurs_on_left && occurs_on_right) return true;
                if (!occurs_on_left && !occurs_on_right) continue;

                if (first_inclusion == nullptr) {
                    first_inclusion = &inclusion;
                    continue;
                }
                if (inclusion != *first_inclusion
                        && inclusion != first_inclusion->get_switched_sides_predicate()) {
                    return true;
                }
            }
            return false;
        };

        BasicTerm cur_var = concatenation[0];
        // we will build an automaton in prev_aut for the variables in prev_division which are pushed into result when needed
        std::shared_ptr<mata::nfa::Nfa> prev_aut = aut_ass.at(cur_var);
        std::vector<BasicTerm> prev_division{ cur_var };
        bool prev_requires_own_division = requires_own_division(cur_var);

        for (std::vector<BasicTerm>::size_type i = 1; i < concatenation.size(); ++i) {
            cur_var = concatenation[i];
            std::shared_ptr<mata::nfa::Nfa> cur_var_aut = aut_ass.at(cur_var);
            bool cur_requires_own_division = requires_own_division(cur_var);

            if (!group_non_length || prev_requires_own_division || cur_requires_own_division) {
                // Push prev_aut and prev_division if grouping is disabled or either adjacent
                // term requires its own division because it is length-sensitive or shared by constraints.
                automata_for_concatenation.push_back(prev_aut);
                divisions.push_back(prev_division);
                STRACE(str_nfa,
                    tout << "Automaton for var(s)";
                    for (const auto &var : prev_division) {
                        tout << " " << var.get_name();
                    }
                    tout << ":" << std::endl
                            << *prev_aut;
                );
                prev_aut = cur_var_aut;
                prev_division = std::vector<BasicTerm>{ cur_var };
            } else {
                // we group the current non-length-aware variable with the non-length-aware vars before
                prev_aut = std::make_shared<mata::nfa::Nfa>(mata::nfa::concatenate(*prev_aut, *cur_var_aut));
                prev_division.push_back(cur_var);
            }

            prev_requires_own_division = cur_requires_own_division;
        }
        // we need to push last automaton into result
        automata_for_concatenation.push_back(prev_aut);
        divisions.push_back(prev_division);
        STRACE(str_nfa,
            tout << "Automaton for var(s)";
            for (const auto &var : prev_division) {
                tout << " " << var.get_name();
            }
            tout << ":" << std::endl << *prev_aut;
        );

        return std::make_pair<std::vector<std::shared_ptr<mata::nfa::Nfa>>,std::vector<std::vector<BasicTerm>>>(std::move(automata_for_concatenation), std::move(divisions));
    }

    namespace {

        enum class CstrOrigin {
            LeftNoodle,
            RightNoodle,
            Derived,
        };

        struct Cstr {
            std::vector<BasicTerm> left;
            std::vector<BasicTerm> right;
            CstrOrigin origin;
            bool active = true;
        };

        enum class OverlapOrientation {
            Prefix,
            Suffix,
        };

        struct OverlapCandidate {
            OverlapOrientation orientation;
            BasicTerm overlap_var;
            BasicTerm shared_segment;
            size_t left_cstr_index;
            size_t right_cstr_index;
        };

        struct OverlapRecognition {
            std::optional<OverlapCandidate> candidate;
            std::optional<Predicate> source_inclusion;
        };

        struct LocalNoodleState {
            SolvingState state;
            std::vector<Cstr> cstrs;
            std::set<Predicate> added_derived_constraints;
            std::set<BasicTerm> substituted_vars;
            std::set<BasicTerm> vars_with_narrowed_aut;
            std::optional<OverlapCandidate> overlap_candidate;
        };

        struct LiveOverlap {
            OverlapCandidate candidate;
            std::vector<BasicTerm> x;
            std::vector<BasicTerm> period;
        };

        SolvingState clone_state_automata(const SolvingState& state) {
            SolvingState copy = state;
            for (auto& [term, aut] : copy.aut_ass) {
                aut = std::make_shared<mata::nfa::Nfa>(*aut);
            }
            return copy;
        }

        LocalNoodleState fork_local_state(const LocalNoodleState& local) {
            LocalNoodleState copy = local;
            copy.state = clone_state_automata(local.state);
            return copy;
        }

        mata::nfa::Nfa create_word_star_nfa(const zstring& word) {
            SASSERT(!word.empty());
            mata::nfa::Nfa result{word.length(), {0}, {0}};
            for (unsigned i = 0; i < word.length(); ++i) {
                result.delta.add(i, word[i], (i + 1) % word.length());
            }
            return result;
        }

        mata::nfa::Nfa create_proper_prefix_nfa(const zstring& word) {
            SASSERT(!word.empty());
            mata::nfa::Nfa result{word.length()};
            result.initial.insert(0);
            for (unsigned i = 0; i < word.length(); ++i) {
                result.final.insert(i);
                if (i + 1 < word.length()) result.delta.add(i, word[i], i + 1);
            }
            return result;
        }

        mata::nfa::Nfa create_proper_suffix_nfa(const zstring& word) {
            SASSERT(!word.empty());
            mata::nfa::Nfa result{word.length()};
            result.final.insert(word.length() - 1);
            for (unsigned i = 0; i < word.length(); ++i) {
                result.initial.insert(i);
                if (i + 1 < word.length()) result.delta.add(i, word[i + 1], i + 1);
            }
            return result;
        }

        mata::nfa::Nfa create_kleene_star_nfa(mata::nfa::Nfa result) {
            const auto initial = result.initial;
            const auto final = result.final;
            for (mata::nfa::State f : final) {
                for (mata::nfa::State i : initial) result.delta.add(f, mata::nfa::EPSILON, i);
            }
            result.remove_epsilon();
            const mata::nfa::State epsilon_state = result.add_state();
            result.initial.insert(epsilon_state);
            result.final.insert(epsilon_state);
            return mata::nfa::reduce(result.trim());
        }

        size_t count_term(const std::vector<BasicTerm>& terms, const BasicTerm& needle) {
            return static_cast<size_t>(std::count(terms.begin(), terms.end(), needle));
        }

        OverlapRecognition recognize_overlap_candidate(
            const SolvingState& state,
            const std::vector<Cstr>& cstrs,
            bool on_cycle,
            bool enabled)
        {
            if (!enabled || !on_cycle) return {};

            std::vector<size_t> left_indices;
            std::vector<size_t> right_indices;
            std::vector<BasicTerm> original_left;
            std::vector<BasicTerm> original_right;
            for (size_t i = 0; i < cstrs.size(); ++i) {
                if (cstrs[i].origin == CstrOrigin::LeftNoodle) {
                    left_indices.push_back(i);
                    original_left.insert(original_left.end(), cstrs[i].left.begin(), cstrs[i].left.end());
                } else if (cstrs[i].origin == CstrOrigin::RightNoodle) {
                    right_indices.push_back(i);
                    original_right.insert(original_right.end(), cstrs[i].right.begin(), cstrs[i].right.end());
                }
            }
            if (original_left.empty() || original_right.empty()) return {};

            auto try_candidate = [&](OverlapOrientation orientation,
                                     const BasicTerm& overlap,
                                     size_t left_index,
                                     size_t right_index)
                    -> std::optional<OverlapRecognition> {
                if (count_term(original_left, overlap) != 1
                        || count_term(original_right, overlap) != 1
                        || !state.aut_ass.contains(overlap)
                        || state.substitution_map.contains(overlap)) {
                    return std::nullopt;
                }

                const Cstr& left_cstr = cstrs[left_index];
                const Cstr& right_cstr = cstrs[right_index];
                if (left_cstr.left != std::vector<BasicTerm>{overlap}
                        || right_cstr.right != std::vector<BasicTerm>{overlap}
                        || left_cstr.right.empty() || right_cstr.left.empty()) {
                    return std::nullopt;
                }

                const BasicTerm& shared = orientation == OverlapOrientation::Prefix
                    ? left_cstr.right.back() : left_cstr.right.front();
                const BasicTerm& other_shared = orientation == OverlapOrientation::Prefix
                    ? right_cstr.left.front() : right_cstr.left.back();
                if (shared != other_shared) return std::nullopt;

                if (!shared.is_variable() || !state.aut_ass.contains(shared)
                        || state.substitution_map.contains(shared)) {
                    return OverlapRecognition{};
                }
                SASSERT(on_cycle);

                OverlapRecognition recognition;
                recognition.candidate =
                    OverlapCandidate{orientation, overlap, shared, left_index, right_index};
                recognition.source_inclusion =
                    Predicate::create_equation(original_left, original_right);
                return recognition;
            };

            if (original_left.front().is_variable()
                    && original_left.front() == original_right.back()) {
                if (std::optional<OverlapRecognition> recognition = try_candidate(
                        OverlapOrientation::Prefix, original_left.front(),
                        left_indices.front(), right_indices.back())) {
                    return *std::move(recognition);
                }
            }
            if (original_left.back().is_variable()
                    && original_left.back() == original_right.front()) {
                if (std::optional<OverlapRecognition> recognition = try_candidate(
                        OverlapOrientation::Suffix, original_left.back(),
                        left_indices.back(), right_indices.front())) {
                    return *std::move(recognition);
                }
            }
            return {};
        }

        std::optional<LiveOverlap> revalidate_overlap(const LocalNoodleState& local) {
            if (!local.overlap_candidate.has_value()) return std::nullopt;
            const OverlapCandidate& candidate = *local.overlap_candidate;
            if (candidate.left_cstr_index >= local.cstrs.size()
                    || candidate.right_cstr_index >= local.cstrs.size()) return std::nullopt;
            const Cstr& left = local.cstrs[candidate.left_cstr_index];
            const Cstr& right = local.cstrs[candidate.right_cstr_index];
            if (!left.active || !right.active
                    || left.origin != CstrOrigin::LeftNoodle
                    || right.origin != CstrOrigin::RightNoodle
                    || left.left != std::vector<BasicTerm>{candidate.overlap_var}
                    || right.right != std::vector<BasicTerm>{candidate.overlap_var}
                    || !local.state.aut_ass.contains(candidate.overlap_var)
                    || !local.state.aut_ass.contains(candidate.shared_segment)) {
                return std::nullopt;
            }

            LiveOverlap live{candidate, {}, {}};
            if (candidate.orientation == OverlapOrientation::Prefix) {
                if (left.right.empty() || right.left.empty()
                        || left.right.back() != candidate.shared_segment
                        || right.left.front() != candidate.shared_segment) return std::nullopt;
                live.period.assign(left.right.begin(), left.right.end() - 1);
                live.x.assign(right.left.begin() + 1, right.left.end());
            } else {
                if (left.right.empty() || right.left.empty()
                        || left.right.front() != candidate.shared_segment
                        || right.left.back() != candidate.shared_segment) return std::nullopt;
                live.period.assign(left.right.begin() + 1, left.right.end());
                live.x.assign(right.left.begin(), right.left.end() - 1);
            }
            for (const BasicTerm& term : live.period) {
                if (term.is_variable() && !local.state.aut_ass.contains(term)) return std::nullopt;
            }
            for (const BasicTerm& term : live.x) {
                if (term.is_variable() && !local.state.aut_ass.contains(term)) return std::nullopt;
            }
            return live;
        }

        void add_derived_constraint(LocalNoodleState& local, std::vector<BasicTerm> residual) {
            SASSERT(!residual.empty());
            Predicate derived = Predicate::create_equation(std::move(residual), {});
            if (local.added_derived_constraints.insert(derived).second) {
                local.cstrs.push_back({derived.get_left_side(), derived.get_right_side(), CstrOrigin::Derived, true});
            }
        }

        void add_split_constraints(
                LocalNoodleState& local,
                std::vector<Predicate::EquationSimplificationResult::EquationSides> split_equations,
                CstrOrigin origin) {
            for (auto& equation : split_equations) {
                local.cstrs.push_back(
                    {std::move(equation.left), std::move(equation.right), origin, true});
            }
        }

        enum class LiteralTransformResult {
            NotApplicable,
            Applied,
            Infeasible,
        };

    }

    std::vector<LocalNoodleResult> process_substituting_inclusions(
        SolvingState state,
        const std::vector<Predicate>& left_inclusions,
        const std::vector<Predicate>& right_inclusions,
        bool on_cycle,
        size_t parent_depth,
        bool enable_overlap_acceleration)
    {
        size_t generated_depth = 0;
        if (on_cycle) {
            if (parent_depth == 0) {
                util::throw_error("On-cycle inclusion has depth zero");
            }
            if (parent_depth == std::numeric_limits<size_t>::max()) {
                util::throw_error("On-cycle inclusion depth overflow");
            }
            generated_depth = parent_depth + 1;
        }
        auto get_acceleration_depth = [parent_depth]() {
            if (parent_depth == 0) {
                util::throw_error("Accelerated inclusion has a depth-zero parent");
            }
            if (parent_depth > std::numeric_limits<size_t>::max() / 2) {
                util::throw_error("Accelerated inclusion depth overflow");
            }
            return parent_depth * 2;
        };

        LocalNoodleState initial;
        initial.state = std::move(state);
        initial.cstrs.reserve(left_inclusions.size() + right_inclusions.size());
        for (const Predicate& predicate : left_inclusions) {
            SASSERT(predicate.is_equation());
            initial.cstrs.push_back({predicate.get_left_side(), predicate.get_right_side(), CstrOrigin::LeftNoodle, true});
        }
        for (const Predicate& predicate : right_inclusions) {
            SASSERT(predicate.is_equation());
            initial.cstrs.push_back({predicate.get_left_side(), predicate.get_right_side(), CstrOrigin::RightNoodle, true});
        }
        std::optional<Predicate> overlap_source_inclusion;
        OverlapRecognition recognition = recognize_overlap_candidate(
            initial.state, initial.cstrs, on_cycle, enable_overlap_acceleration);
        if (recognition.candidate.has_value()) {
            initial.overlap_candidate = std::move(recognition.candidate);
            overlap_source_inclusion = std::move(recognition.source_inclusion);
        }

        const size_t initial_cstr_count = initial.cstrs.size();
        for (size_t i = 0; i < initial_cstr_count; ++i) {
            const CstrOrigin origin = initial.cstrs[i].origin;
            Predicate::EquationSimplificationResult result =
                Predicate::simplify_equation(initial.cstrs[i].left, initial.cstrs[i].right);
            if (result.kind == Predicate::EquationSimplificationResult::Kind::Infeasible) {
                return {};
            }
            if (result.kind == Predicate::EquationSimplificationResult::Kind::EmptySideConsequence) {
                add_derived_constraint(initial, std::move(result.residual));
            }
            add_split_constraints(initial, std::move(result.split_equations), origin);
        }

        std::vector<LocalNoodleResult> results;
        std::function<void(LocalNoodleState)> process_branch;
        process_branch = [&](LocalNoodleState local) {
        auto apply_sub = [&](const BasicTerm& var) -> bool {
            const std::vector<BasicTerm>& repl = local.state.substitution_map.at(var);
            std::vector<std::vector<BasicTerm>> derived_constraints;
            std::vector<Cstr> split_constraints;
            const size_t cstr_count = local.cstrs.size();
            for (size_t i = 0; i < cstr_count; ++i) {
                Cstr& c = local.cstrs[i];
                if (!c.active) continue;
                Predicate::EquationSimplificationResult result =
                    Predicate::apply_subst_eq(var, repl, c.left, c.right);
                if (result.kind == Predicate::EquationSimplificationResult::Kind::Infeasible) {
                    return false;
                }
                if (result.kind == Predicate::EquationSimplificationResult::Kind::EmptySideConsequence) {
                    derived_constraints.push_back(std::move(result.residual));
                }
                for (auto& equation : result.split_equations) {
                    split_constraints.push_back(
                        {std::move(equation.left), std::move(equation.right), c.origin, true});
                }
            }
            for (auto& residual : derived_constraints) {
                add_derived_constraint(local, std::move(residual));
            }
            for (Cstr& split : split_constraints) {
                local.cstrs.push_back(std::move(split));
            }
            return true;
        };

        auto do_sub = [&](const BasicTerm& var, const std::vector<BasicTerm>& replacement) -> bool {
            if (local.state.substitution_map.contains(var)) {
                return apply_sub(var);
            }
            STRACE(str, tout << "Substituting " << var << " with ";
                for (const BasicTerm& t : replacement) {
                    tout << t << " ";
                }
                tout << std::endl;);
            if (local.state.aut_ass.count(var) > 0) {
                if (replacement.empty()) {
                    if (!local.state.aut_ass.contains_epsilon(var)) return false;
                } else if (replacement.size() == 1 && replacement[0].is_literal()) {
                    if (!local.state.aut_ass.contains_literal(var, replacement[0])) return false;
                } else if (replacement.size() == 1 && replacement[0].is_variable()) {
                    const BasicTerm& kept = replacement[0];
                    if (local.state.aut_ass.count(kept) > 0) {
                        if (local.vars_with_narrowed_aut.contains(var))
                            local.vars_with_narrowed_aut.insert(kept);
                        if (!mata::nfa::is_included(*local.state.aut_ass.at(kept), *local.state.aut_ass.at(var))) {
                            local.vars_with_narrowed_aut.insert(kept);
                            STRACE(str, tout << "Narrowing automaton for " << kept << std::endl;);
                            auto intersect = std::make_shared<mata::nfa::Nfa>(
                                mata::nfa::reduce(mata::nfa::intersection(
                                    *local.state.aut_ass.at(var), *local.state.aut_ass.at(kept)).trim()));
                            if (intersect->is_lang_empty()) return false;
                            local.state.aut_ass[kept] = std::move(intersect);
                        }
                    }
                }
            }
            std::vector<BasicTerm> flat_replacement;
            flat_replacement.reserve(replacement.size());
            for (const BasicTerm& t : replacement) {
                auto it = local.state.substitution_map.find(t);
                if (it != local.state.substitution_map.end()) {
                    flat_replacement.insert(flat_replacement.end(), it->second.begin(), it->second.end());
                } else {
                    flat_replacement.push_back(t);
                }
            }
            if (local.state.length_sensitive_vars.contains(var)) {
                local.state.mark_length_sensitive(flat_replacement);
            }
            local.state.substitution_map[var] = flat_replacement;
            local.state.aut_ass.erase(var);
            local.substituted_vars.insert(var);
            for (auto& [key, vals] : local.state.substitution_map) {
                if (key == var) continue;
                std::vector<BasicTerm> new_vals;
                bool changed = false;
                for (const BasicTerm& t : vals) {
                    if (t == var) {
                        new_vals.insert(new_vals.end(), flat_replacement.begin(), flat_replacement.end());
                        changed = true;
                    } else {
                        new_vals.push_back(t);
                    }
                }
                if (changed) vals = std::move(new_vals);
            }
            return apply_sub(var);
        };

        auto deactivate_overlap = [&](const LiveOverlap& live) {
            SASSERT(overlap_source_inclusion.has_value());
            local.state.remove_predicate_everywhere(
                overlap_source_inclusion->get_switched_sides_predicate());
            local.cstrs[live.candidate.left_cstr_index].active = false;
            local.cstrs[live.candidate.right_cstr_index].active = false;
            local.overlap_candidate.reset();
        };

        auto add_carrier = [&](const std::vector<BasicTerm>& factor, const BasicTerm& shared_segment) {
            Predicate carrier = local.state.add_inclusion(factor, {shared_segment}, false);
            local.state.enqueue_predicate(carrier, true);
        };

        auto add_noodle_residual = [&](std::vector<BasicTerm> left,
                                       std::vector<BasicTerm> right,
                                       bool enqueue_forward) {
            Predicate residual = local.state.add_inclusion(
                std::move(left), std::move(right), on_cycle, generated_depth);
            if (enqueue_forward) {
                local.state.enqueue_predicate(residual, !on_cycle);
            }
            if (on_cycle) {
                Predicate reverse = residual.get_switched_sides_predicate();
                local.state.add_predicate(reverse, true, generated_depth);
                local.state.enqueue_predicate(reverse, false);
            }
        };

        auto apply_general_acceleration = [&](const LiveOverlap& live, mata::nfa::Nfa period_aut) -> bool {
            const BasicTerm& a = live.candidate.overlap_var;
            if (!local.state.aut_ass.contains(a)) return false;
            const size_t acceleration_depth = get_acceleration_depth();
            deactivate_overlap(live);

            const bool old_is_length = local.state.length_sensitive_vars.contains(a);
            BasicTerm a1 = local.state.add_fresh_var(
                std::make_shared<mata::nfa::Nfa>(create_kleene_star_nfa(std::move(period_aut))),
                "period", old_is_length, false);
            BasicTerm a2 = local.state.add_fresh_var(
                std::make_shared<mata::nfa::Nfa>(local.state.aut_ass.sigma_star_automaton()),
                "remainder", old_is_length, false);
            BasicTerm v = local.state.add_fresh_var(
                std::make_shared<mata::nfa::Nfa>(local.state.aut_ass.sigma_star_automaton()),
                "overlap_factor", false, false);

            std::vector<BasicTerm> factor;
            std::vector<BasicTerm> replacement;
            if (live.candidate.orientation == OverlapOrientation::Prefix) {
                factor = {a1, a2};
                replacement = live.period;
                replacement.insert(replacement.end(), factor.begin(), factor.end());
            } else {
                factor = {a2, a1};
                replacement = factor;
                replacement.insert(replacement.end(), live.period.begin(), live.period.end());
            }
            add_carrier(factor, live.candidate.shared_segment);

            auto add_factor_equality = [&](const std::vector<BasicTerm>& left,
                                           const std::vector<BasicTerm>& right) {
                Predicate forward = local.state.add_inclusion(
                    left, right, true, acceleration_depth);
                Predicate reverse = local.state.add_inclusion(
                    right, left, true, acceleration_depth);
                local.state.enqueue_predicate(forward, false);
                local.state.enqueue_predicate(reverse, false);
            };

            const std::vector<BasicTerm> a2_v{a2, v};
            const std::vector<BasicTerm> v_a2{v, a2};
            if (live.candidate.orientation == OverlapOrientation::Prefix) {
                add_factor_equality(a2_v, live.period);
                add_factor_equality(live.x, v_a2);
            } else {
                add_factor_equality(live.x, a2_v);
                add_factor_equality(v_a2, live.period);
            }

            std::vector<BasicTerm> a1_period{a1};
            a1_period.insert(a1_period.end(), live.period.begin(), live.period.end());
            std::vector<BasicTerm> period_a1 = live.period;
            period_a1.push_back(a1);
            Predicate commute_forward = local.state.add_inclusion(a1_period, period_a1, true, acceleration_depth);
            Predicate commute_reverse = local.state.add_inclusion(period_a1, a1_period, true, acceleration_depth);
            local.state.enqueue_predicate(commute_forward, false);
            local.state.enqueue_predicate(commute_reverse, false);

            if (old_is_length) {
                local.state.mark_length_sensitive({live.candidate.shared_segment});
            }

            return do_sub(a, replacement);
        };

        auto apply_literal_acceleration = [&](const LiveOverlap& live) -> LiteralTransformResult {
            zstring x_word;
            zstring period_word;
            const bool x_is_literal = util::is_concatenation_of_literals(live.x, x_word);
            const bool period_is_literal =
                util::is_concatenation_of_literals(live.period, period_word);
            if (!x_is_literal && !period_is_literal) return LiteralTransformResult::NotApplicable;

            bool use_period = false;
            zstring word;
            if (x_is_literal && period_is_literal) {
                if (x_word.length() != period_word.length()) return LiteralTransformResult::Infeasible;
                if (x_word.empty()) return LiteralTransformResult::NotApplicable;
                use_period = true;
                word = period_word;
            } else if (period_is_literal && !period_word.empty()) {
                use_period = true;
                word = period_word;
            } else if (x_is_literal && !x_word.empty()) {
                use_period = false;
                word = x_word;
            } else {
                return LiteralTransformResult::NotApplicable;
            }

            const BasicTerm& a = live.candidate.overlap_var;
            if (!local.state.aut_ass.contains(a)) return LiteralTransformResult::Infeasible;
            const size_t acceleration_depth = get_acceleration_depth();
            deactivate_overlap(live);
            const bool old_is_length = local.state.length_sensitive_vars.contains(a);
            BasicTerm a1 = local.state.add_fresh_var(
                std::make_shared<mata::nfa::Nfa>(create_word_star_nfa(word)),
                "overlap_star", old_is_length, false);

            const bool prefix_remainder =
                (live.candidate.orientation == OverlapOrientation::Prefix && use_period)
                || (live.candidate.orientation == OverlapOrientation::Suffix && !use_period);
            BasicTerm a2 = local.state.add_fresh_var(
                std::make_shared<mata::nfa::Nfa>(prefix_remainder
                    ? create_proper_prefix_nfa(word) : create_proper_suffix_nfa(word)),
                prefix_remainder ? "overlap_prefix" : "overlap_suffix",
                old_is_length, false);

            const bool star_first = prefix_remainder;
            std::vector<BasicTerm> factor = star_first
                ? std::vector<BasicTerm>{a1, a2}
                : std::vector<BasicTerm>{a2, a1};

            const BasicTerm word_term(BasicTermType::Literal, word);
            std::vector<BasicTerm> replacement;
            if (prefix_remainder) {
                replacement = {word_term};
                replacement.insert(replacement.end(), factor.begin(), factor.end());
            } else {
                replacement = factor;
                replacement.push_back(word_term);
            }
            add_carrier(factor, live.candidate.shared_segment);

            std::vector<BasicTerm> residual_left;
            std::vector<BasicTerm> residual_right;
            if (live.candidate.orientation == OverlapOrientation::Prefix && use_period) {
                residual_left = {a2};
                residual_left.insert(residual_left.end(), live.x.begin(), live.x.end());
                residual_right = {word_term, a2};
            } else if (live.candidate.orientation == OverlapOrientation::Prefix) {
                residual_left = {a2, word_term};
                residual_right = live.period;
                residual_right.push_back(a2);
            } else if (!use_period) {
                residual_left = {word_term, a2};
                residual_right = {a2};
                residual_right.insert(residual_right.end(), live.period.begin(), live.period.end());
            } else {
                residual_left = live.x;
                residual_left.push_back(a2);
                residual_right = {a2, word_term};
            }
            Predicate residual_forward = local.state.add_inclusion(
                residual_left, residual_right, true, acceleration_depth);
            local.state.enqueue_predicate(residual_forward, false);
            Predicate residual_reverse =
                local.state.add_inclusion(residual_right, residual_left, true, acceleration_depth);
            local.state.enqueue_predicate(residual_reverse, false);
            if (old_is_length) {
                local.state.mark_length_sensitive({live.candidate.shared_segment});
            }
            return do_sub(a, replacement)
                ? LiteralTransformResult::Applied : LiteralTransformResult::Infeasible;
        };

        for (;;) {
            int best = -1, best_prio = 0;
            for (int i = 0; i < (int)local.cstrs.size(); i++) {
                if (!local.cstrs[i].active) continue;
                auto& c = local.cstrs[i];
                if (c.left.empty() && c.right.empty()) {
                    local.cstrs[i].active = false;
                    continue;
                }
                int prio = 0;
                if (c.left.empty() || c.right.empty()) {
                    prio = 3;
                } else if (c.left.size() + c.right.size() == 2) {
                    prio = (c.left[0].is_literal() || c.right[0].is_literal()) ? 2 : 1;
                }
                if (prio > best_prio) {
                    best = i;
                    best_prio = prio;
                    if (best_prio == 3) break; // can't beat empty-side priority
                }
            }
            if (best != -1) {
                Cstr c = local.cstrs[best];
                local.cstrs[best].active = false;

                if (c.left == c.right) continue;

                if (c.left.empty() || c.right.empty()) {
                    const auto& other = c.left.empty() ? c.right : c.left;
                    for (const BasicTerm& t : other) {
                        if (t.is_literal() && !t.get_name().empty()) return;
                    }
                    for (const BasicTerm& t : other) {
                        if (t.is_variable() && !do_sub(t, {})) return;
                    }
                } else {
                    const BasicTerm& l = c.left[0];
                    const BasicTerm& r = c.right[0];
                    if (l == r) continue;
                    if (l.is_literal() && r.is_literal()) {
                        return;
                    } else if (l.is_literal()) {
                        if (!do_sub(r, {l})) return;
                    } else if (r.is_literal()) {
                        if (!do_sub(l, {r})) return;
                    } else {
                        if (c.origin == CstrOrigin::LeftNoodle) {
                            if (!do_sub(r, {l})) return;
                        } else {
                            SASSERT(c.origin == CstrOrigin::RightNoodle);
                            if (!do_sub(l, {r})) return;
                        }
                    }
                }
                continue;
            }

            if (local.overlap_candidate.has_value()) {
                std::optional<LiveOverlap> live = revalidate_overlap(local);
                if (!live.has_value()) {
                    local.overlap_candidate.reset();
                } else {
                    LiteralTransformResult literal_result = apply_literal_acceleration(*live);
                    if (literal_result == LiteralTransformResult::Infeasible) return;
                    if (literal_result == LiteralTransformResult::Applied) continue;

                    mata::nfa::Nfa period_aut = local.state.aut_ass.get_automaton_concat(live->period);
                    const mata::nfa::Nfa epsilon_aut = mata::nfa::builder::create_empty_string_nfa();
                    const bool accepts_nonempty = !mata::nfa::is_included(period_aut, epsilon_aut);
                    if (!accepts_nonempty) {
                        local.overlap_candidate.reset();
                    } else {
                        if (period_aut.is_in_lang(mata::Word{})) {
                            LocalNoodleState epsilon_branch = fork_local_state(local);
                            epsilon_branch.overlap_candidate.reset();
                            add_derived_constraint(epsilon_branch, live->period);
                            process_branch(std::move(epsilon_branch));
                        }
                        if (!apply_general_acceleration(*live, std::move(period_aut))) return;
                        continue;
                    }
                }
            }

            int residual_index = -1;
            for (int i = 0; i < (int)local.cstrs.size(); ++i) {
                if (local.cstrs[i].active) {
                    residual_index = i;
                    break;
                }
            }
            if (residual_index == -1) break;

            Cstr c = local.cstrs[residual_index];
            local.cstrs[residual_index].active = false;
            if (c.left == c.right) continue;
            SASSERT(c.origin != CstrOrigin::Derived);

            const bool from_left = c.origin == CstrOrigin::LeftNoodle;
            const std::vector<BasicTerm>& orig  = from_left ? c.left  : c.right;
            const std::vector<BasicTerm>& fresh = from_left ? c.right : c.left;
            if (orig.size() == 1 && orig[0].is_variable() && !local.vars_with_narrowed_aut.contains(orig[0])
                    && (from_left || on_cycle || local.state.contains_length_var(orig))) {
                const BasicTerm orig_var = orig[0];
                const std::vector<BasicTerm> fresh_copy(fresh);
                
                if (local.state.substitution_map.contains(orig_var)) {
                    add_noodle_residual(
                        local.state.substitution_map.at(orig_var), fresh_copy, true);
                } else if (!do_sub(orig_var, fresh_copy)) return;
            } else {
                add_noodle_residual(
                    c.left, c.right,
                    from_left || on_cycle || local.state.contains_length_var(orig));
            }
        }

        std::set<BasicTerm> vars_with_changed_language = local.substituted_vars;
        vars_with_changed_language.insert(
            local.vars_with_narrowed_aut.begin(), local.vars_with_narrowed_aut.end());
        local.state.push_dependent_predicates(vars_with_changed_language, on_cycle);
        if (!local.state.substitute_vars(local.substituted_vars)) return;
        local.state.push_non_simple_transducers_to_processing();
        results.push_back(LocalNoodleResult{
            std::move(local.state), std::move(local.substituted_vars)
        });
        };

        process_branch(std::move(initial));
        return results;
    }

    BasicTerm SolvingState::add_fresh_var(std::shared_ptr<mata::nfa::Nfa> nfa, std::string var_prefix, bool is_length, bool optimize_literal) {
        if (zstring literal; optimize_literal && AutAssignment::aut_encodes_literal(*nfa, literal)) {
            BasicTerm new_literal{BasicTermType::Literal, literal};
            aut_ass[new_literal] = nfa;
            return new_literal;
        } else {
            BasicTerm new_var = util::mk_noodler_var_fresh(var_prefix);
            aut_ass[new_var] = nfa;
            if (is_length) { length_sensitive_vars.insert(new_var); }
            return new_var;
        }
    }

    void SolvingState::replace_dummy_symbol_in_transducers_with(std::set<mata::Symbol> replacements) {
        if (replacements.empty()) { return; }
        for (const Predicate& trans : transducers) {
            util::replace_dummy_symbol_in_transducer_with(*trans.get_transducer(), replacements);
        }
    }

    std::string SolvingState::print_to_DOT() const {
        auto escape_DOT_string = [](std::string string_to_escape) {
            std::ostringstream res;
            for (char c : string_to_escape) {
                if (c == '\\' || c == '{' || c == '}' || c == '<' || c == '>' || c == '|' || c == '\"' || c == ' ') {
                    res << '\\' << c;
                } else {
                    res << c;
                }
            }
            return res.str();
        };

        auto print_predicate_to_DOT = [this,&escape_DOT_string](const Predicate& pred) {
            std::ostringstream res;
            if (pred.is_equation()) { // inclusion
                res << escape_DOT_string(to_string(pred.get_left_side())) << "\\ ⊆\\ " << escape_DOT_string(to_string(pred.get_right_side()));
            } else { //transducer
                SASSERT(pred.is_transducer());
                res << escape_DOT_string(to_string(pred.get_output())) << "\\ =\\ T" << pred.get_transducer().get() << "(" << escape_DOT_string(to_string(pred.get_input())) << ")";
            }
            if (is_predicate_on_cycle(pred)) {
                res << "\\ :\\ oncycle";
            }
            return res.str();
        };
        
        auto print_strings = [](std::vector<std::string>& strings, bool order, std::string del = "\\n") {
            if (order) {
                std::sort(strings.begin(), strings.end());
            }
            bool first = true;
            std::ostringstream res;
            for (const std::string& string : strings) {
                if (first) {
                    first = false;
                    res << string;
                } else {
                    res << del << string;
                }
            }
            return res.str(); 
        };

        auto print_predicate_container_to_DOT = [&print_predicate_to_DOT, &print_strings]<typename T>(const T& predicate_container, bool order) {
            std::vector<std::string> predicate_strings(predicate_container.size());
            std::transform(predicate_container.begin(), predicate_container.end(), predicate_strings.begin(), print_predicate_to_DOT);
            return print_strings(predicate_strings, order);
        };


        auto print_vars_to_DOT = [&escape_DOT_string, &print_strings]<typename T>(const T& vars, bool order, bool delimit_by_space) {
            std::vector<std::string> var_names(vars.size());
            std::transform(vars.begin(), vars.end(), var_names.begin(), [&escape_DOT_string](const BasicTerm& var) { return escape_DOT_string(var.to_string());});
            return print_strings(var_names, order, (delimit_by_space ? "\\ " : "\\n"));
        };

        std::ostringstream res;
        res << DOT_name << "[shape=record,label=\"" << print_predicate_container_to_DOT(inclusions, true);
        if (!inclusions.empty() && !transducers.empty()) {
            res << "\\n";
        }
        res << print_predicate_container_to_DOT(transducers, true) << "|" << print_predicate_container_to_DOT(predicates_to_process, false) << "|";

        std::vector<std::string> strings_to_print;
        for (const auto& [var,subst_vars] : substitution_map) {
            strings_to_print.push_back(escape_DOT_string(var.to_string()) + std::string("\\ -\\>\\ ") + print_vars_to_DOT(subst_vars, false, true));
        }
        for (const BasicTerm& var : aut_ass.get_keys()) {
            if (!var.is_literal()) { 
                strings_to_print.push_back(escape_DOT_string(var.to_string()) + std::string("\\ -\\>\\ NFA"));
            }
        }
        res << print_strings(strings_to_print, true);

        res << "|";

        res << print_vars_to_DOT(length_sensitive_vars, true, false);

        res << "\"];";
        return res.str();
    }

}
