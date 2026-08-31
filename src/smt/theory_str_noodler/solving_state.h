#ifndef _NOODLER_SOLVING_STATE_H_
#define _NOODLER_SOLVING_STATE_H_

#include <memory>
#include <vector>
#include <algorithm>
#include <optional>
#include <map>

#include "params/theory_str_noodler_params.h"
#include "formula.h"
#include "aut_assignment.h"
#include "util.h"

namespace smt::noodler {

    /**
     * @brief A priority queue for predicates used in the decision procedure worklist.
     *
     * Elements with priority flag p=true are dequeued first and in insertion order.
     * Lower-priority elements are dequeued by increasing on-cycle depth, then by
     * increasing weight (the sum of all parameter-list lengths). Insertion
     * enforces uniqueness. Re-pushing a predicate with a smaller depth updates
     * and repositions a lower-priority entry. When the heuristic is disabled,
     * all elements are dequeued in insertion order.
     */
    class PredicateQueue {
    public:
        struct Entry {
            Predicate predicate;
            bool high_priority;
            std::optional<size_t> depth;
        };

    private:
        std::vector<Entry> data_; // ordered with the next entry to pop at the front
        bool heuristic_enabled_ = true;

        static size_t pred_weight(const Predicate& pred) {
            size_t w = 0;
            for (const auto& param : pred.get_params())
                w += param.size();
            return w;
        }

        /// Returns true if a new entry @p a should be inserted before queued entry @p b.
        static bool is_better(const Entry& a, const Entry& b) {
            if (a.high_priority != b.high_priority)
                return a.high_priority > b.high_priority;
            if (a.high_priority) return false;
            const size_t a_depth = a.depth.value_or(0);
            const size_t b_depth = b.depth.value_or(0);
            if (a_depth != b_depth) return a_depth < b_depth;
            return pred_weight(a.predicate) < pred_weight(b.predicate);
        }

    public:
        PredicateQueue() = default;
        explicit PredicateQueue(bool heuristic_enabled)
            : heuristic_enabled_(heuristic_enabled) {}

        [[nodiscard]] bool heuristic_enabled() const { return heuristic_enabled_; }

        /// Replace the depth metadata of an existing entry and restore normal ordering.
        bool set_depth_if_present(const Predicate& pred, std::optional<size_t> depth) {
            auto it = std::find_if(data_.begin(), data_.end(),
                [&](const Entry& entry) { return entry.predicate == pred; });
            if (it == data_.end()) return false;
            it->depth = depth;
            if (!heuristic_enabled_ || it->high_priority) return true;
            Entry updated = std::move(*it);
            data_.erase(it);
            auto pos = std::find_if(data_.begin(), data_.end(),
                [&](const Entry& entry) { return is_better(updated, entry); });
            data_.insert(pos, std::move(updated));
            return true;
        }

        /**
         * @brief Push @p pred with priority @p p.
         *
         * Skips if an entry with the same predicate already exists, except that a
         * smaller supplied depth is retained and a lower-priority entry is repositioned.
         * High-priority entries are dequeued in insertion order. Lower-priority entries
         * are dequeued by increasing depth and weight, preserving insertion order for ties.
         */
        void push(const Predicate& pred, bool p, std::optional<size_t> depth = std::nullopt) {
            for (auto it = data_.begin(); it != data_.end(); ++it) {
                if (it->predicate != pred) continue;
                if (!depth.has_value()
                        || (it->depth.has_value() && *it->depth <= *depth)) return;
                set_depth_if_present(pred, depth);
                return;
            }
            Entry entry{pred, p, depth};
            if (!heuristic_enabled_) {
                data_.push_back(std::move(entry));
                return;
            }
            auto pos = std::find_if(data_.begin(), data_.end(),
                [&](const Entry& e) { return is_better(entry, e); });
            data_.insert(pos, std::move(entry));
        }

        /// Returns the highest-priority predicate (the one that will be popped next).
        [[nodiscard]] const Predicate& top() const { return data_.front().predicate; }

        /// Returns the priority flag of the front element.
        [[nodiscard]] bool top_priority() const { return data_.front().high_priority; }

        /// Returns the on-cycle depth of the front element, if it has one.
        [[nodiscard]] std::optional<size_t> top_depth() const { return data_.front().depth; }

        /// Removes the front element.
        void pop() { data_.erase(data_.begin()); }

        /// Removes @p pred while preserving the order and priorities of other entries.
        bool erase(const Predicate& pred) {
            auto it = std::find_if(data_.begin(), data_.end(),
                [&](const Entry& entry) { return entry.predicate == pred; });
            if (it == data_.end()) return false;
            data_.erase(it);
            return true;
        }

        [[nodiscard]] bool empty() const { return data_.empty(); }
        [[nodiscard]] size_t size() const { return data_.size(); }

        /// Iterator that dereferences to const Predicate& (hides the bool flag).
        struct const_iterator {
            using InnerIt = typename std::vector<Entry>::const_iterator;
            InnerIt it_;
            explicit const_iterator(InnerIt it) : it_(it) {}
            const Predicate& operator*()  const { return it_->predicate; }
            const Predicate* operator->() const { return &it_->predicate; }
            const_iterator& operator++() { ++it_; return *this; }
            const_iterator  operator++(int) { auto tmp = *this; ++it_; return tmp; }
            bool operator==(const const_iterator& o) const { return it_ == o.it_; }
            bool operator!=(const const_iterator& o) const { return it_ != o.it_; }
        };

        [[nodiscard]] const_iterator begin() const { return const_iterator(data_.begin()); }
        [[nodiscard]] const_iterator end()   const { return const_iterator(data_.end()); }
    };

    /// A state of decision procedure that can lead to a solution
    struct SolvingState {

    private:
        
        /// @brief Apply substitutions from substitution_map directly to disequations.
        void apply_substitutions_to_disequations();

    public:
        // aut_ass[x] assigns variable x to some automaton while substitution_map[x] maps variable x to
        // the concatenation of variables for which x was substituted (i.e. its automaton is concatenation
        // of the automata from these variables). Each variable is either assigned in aut_ass or
        // substituted in substitution_map, but not both!
        AutAssignment aut_ass;
        std::unordered_map<BasicTerm, std::vector<BasicTerm>> substitution_map;

        // set of inclusions (i.e. Predicate must be of type equations which we pretend is an inclusion) where we are trying to find aut_ass + substitution_map such that they hold
        std::set<Predicate> inclusions;
        // set of transducers which we want to smiplify so that we only have at most one var in input and at most one var in output
        std::set<Predicate> transducers;

        // set of inclusions/transducers from the previous sets that for sure are not on cycle in the inclusion graph
        // that would be generated from inclusions
        std::set<Predicate> predicates_not_on_cycle;

        // Generation depth of each persistent on-cycle inclusion.
        std::map<Predicate, size_t> inclusion_depths;

        // contains inclusions/transducers we need to process (for inclusions we want them to hold under aut_ass and substitution_map, for transducers we want to simplify them)
        PredicateQueue predicates_to_process;

        // the variables that have length constraint on them in the rest of formula
        std::unordered_set<BasicTerm> length_sensitive_vars;

        // disequations postponed to be handled after finding stable solutions
        Formula postponed_disequations;

        // conversions local to this solving state
        std::vector<TermConversion> conversions;

        // length conjuncts generated while replacing disequalities in this state
        std::vector<LenNode> disequations_len_formula_conjuncts;

        // indicates whether this solving state has any siblings in the solving state tree
        bool has_siblings = false;

        SolvingState() = default;
        SolvingState(AutAssignment aut_ass,
                     PredicateQueue predicates_to_process,
                     std::set<Predicate> inclusions,
                     std::set<Predicate> transducers,
                     std::set<Predicate> predicates_not_on_cycle,
                     std::unordered_set<BasicTerm> length_sensitive_vars,
                     std::unordered_map<BasicTerm, std::vector<BasicTerm>> substitution_map,
                     bool has_siblings,
                     Formula disequations = {},
                     std::vector<TermConversion> conversions = {})
                        : aut_ass(aut_ass),
                          substitution_map(substitution_map),
                          inclusions(inclusions),
                          transducers(transducers),
                          predicates_not_on_cycle(predicates_not_on_cycle),
                          predicates_to_process(predicates_to_process),
                          length_sensitive_vars(length_sensitive_vars),
                          postponed_disequations(disequations),
                          conversions(conversions),
                          has_siblings(has_siblings) {
            for (const Predicate& inclusion : this->inclusions) {
                if (!this->predicates_not_on_cycle.contains(inclusion)) {
                    inclusion_depths.emplace(inclusion, 1);
                    this->predicates_to_process.set_depth_if_present(inclusion, 1);
                }
            }
        }

        /// Enqueue a persistent predicate with its recorded on-cycle depth.
        void enqueue_predicate(const Predicate& predicate, bool high_priority) {
            std::optional<size_t> depth;
            if (predicate.is_equation() && is_predicate_on_cycle(predicate)) {
                depth = get_inclusion_depth(predicate);
            }
            predicates_to_process.push(predicate, high_priority, depth);
        }

        /**
         * @brief Pushes predicates that depend on any variable in @p vars_to_check_dependency.
         * 
         * More concretely, it pushes all predicates whose right side (for inclusion) or inputs (for transducers)
         * contain some variable from @p vars_to_check_dependency.
         * It pushes the predicate only if it is not pushed already.
         * 
         * @param to_back whether to push to front or back to predicates_to_process
         */
        void push_dependent_predicates(std::set<BasicTerm> vars_to_check_dependency, bool to_back) {
            for (const Predicate &inclusion : inclusions) {
                if (is_dependent(vars_to_check_dependency, inclusion.get_right_set())) {
                    enqueue_predicate(inclusion, !to_back);
                }
            }
            for (const Predicate &transducer : transducers) {
                if (is_dependent(vars_to_check_dependency, transducer.get_set_of_param(0))) {
                    enqueue_predicate(transducer, !to_back);
                }
            }
        }

        /**
         * Pushes predicates that would depend on the given @p predicate in the inclusion graph for processing
         * 
         * More concretely, it pushes all predicates whose right side (for inclusion) or inputs (for transducers)
         * contain some variable from the left side/outputs of the given @p predicate.
         * It pushes the predicate only if it is not pushed already.
         */
        void push_dependent_predicates(const Predicate &predicate, bool to_back) {
            std::set<BasicTerm> vars_to_check_dependency;
            if (predicate.is_equation()) { // inclusion
                vars_to_check_dependency = predicate.get_left_set();
            } else {
                SASSERT(predicate.is_transducer());
                vars_to_check_dependency = predicate.get_set_of_param(1);
            }
            
            push_dependent_predicates(vars_to_check_dependency, to_back);
        }

        /**
         * @brief Adds all transducers that contain length vars on input and are not simple (they do not have one input and one output var, or output is literal) back to processing.
         * 
         * It pushes a transducer only if it is not pushed already.
         * Useful after calling substitute_vars().
         */
        void push_non_simple_transducers_to_processing() {
            for (const Predicate &transducer : transducers) {
                if (contains_length_var(transducer.get_input()) && (transducer.get_input().size() != 1 || transducer.get_output().size() != 1 || transducer.get_output()[0].is_literal())) {
                    enqueue_predicate(transducer, true); // push_unique(t, false) = push to front = high priority
                }
            }
        }

        /**
         * Checks whether @p predicate would be on cycle in the inclusion graph (can overapproximate
         * and say that predicate is on cycle even if it is not).
         */
        bool is_predicate_on_cycle(const Predicate &predicate) const {
            return !predicates_not_on_cycle.contains(predicate);
        }

        [[nodiscard]] size_t get_inclusion_depth(const Predicate& inclusion) const {
            SASSERT(inclusion.is_equation());
            SASSERT(is_predicate_on_cycle(inclusion));
            SASSERT(inclusion_depths.contains(inclusion));
            return inclusion_depths.at(inclusion);
        }

        /**
         * Adds @p predicate to this solving state 
         * 
         * @param predicate Predicate to add
         * @param is_on_cycle Whether the predicate would be on cycle in the inclusion graph (if not sure, set to true)
         */
        void add_predicate(Predicate predicate, bool is_on_cycle = true, size_t depth = 1) {
            if (!is_on_cycle) {
                predicates_not_on_cycle.insert(predicate);
                inclusion_depths.erase(predicate);
                predicates_to_process.set_depth_if_present(predicate, std::nullopt);
            }
            if (predicate.is_equation()) { // inclusion
                auto [it, inserted] = inclusions.insert(predicate);
                if (!predicates_not_on_cycle.contains(predicate)) {
                    auto [depth_it, depth_inserted] = inclusion_depths.emplace(*it, depth);
                    if (!depth_inserted && depth < depth_it->second) {
                        depth_it->second = depth;
                        predicates_to_process.set_depth_if_present(*it, depth);
                    }
                }
            } else {
                SASSERT(predicate.is_transducer());
                transducers.insert(std::move(predicate));
            }
        }

        /**
         * Adds inclusion with sides @p left_side and @p right_side to this solving state (i.e. we will start checking if
         * this inclusion should not be added to inclusion_to_process during the decision procedure).
         * 
         * @param left_side Left side of the new inclusion
         * @param right_side Right side of the new inclusion
         * @param is_on_cycle Whether the inclusion would be on cycle in the inclusion graph (if not sure, set to true)
         * @return The newly added inclusion
         */
        Predicate add_inclusion(std::vector<BasicTerm> left_side, std::vector<BasicTerm> right_side,
                                bool is_on_cycle = true, size_t depth = 1) {
            Predicate new_inclusion = Predicate::create_equation(std::move(left_side), std::move(right_side));
            add_predicate(new_inclusion, is_on_cycle, depth);
            return new_inclusion;
        }

        /**
         * Adds transducer @p trans with ipnut variables in @p input and output variables in @p output to this solving state (i.e. we will start checking if
         * this transducer should not be added to inclusion_to_process during the decision procedure).
         * 
         * @param input Input variables
         * @param ouptut Output variables
         * @param is_on_cycle Whether the transducer would be on cycle in the inclusion graph (if not sure, set to true)
         * @return The newly added transducer predicate
         */
        Predicate add_transducer(std::shared_ptr<mata::nft::Nft> trans, std::vector<BasicTerm> input, std::vector<BasicTerm> output, bool is_on_cycle = true) {
            Predicate new_transducer = Predicate::create_transducer(trans, std::move(input), std::move(output));
            add_predicate(new_transducer, is_on_cycle);
            return new_transducer;
        }

        void remove_predicate(const Predicate &predicate) {
            if (predicate.is_equation()) { // inclusion
                inclusions.erase(predicate);
            } else {
                SASSERT(predicate.is_transducer());
                transducers.erase(predicate);
            }
            predicates_not_on_cycle.erase(predicate);
            inclusion_depths.erase(predicate);
        }

        /// Removes a predicate from every persistent state component, including the queue.
        bool remove_predicate_everywhere(const Predicate& predicate) {
            bool removed = false;
            if (predicate.is_equation()) {
                removed = inclusions.erase(predicate) > 0;
            } else {
                SASSERT(predicate.is_transducer());
                removed = transducers.erase(predicate) > 0;
            }
            predicates_not_on_cycle.erase(predicate);
            predicates_to_process.erase(predicate);
            inclusion_depths.erase(predicate);
            return removed;
        }

        /** Mark variables as length-sensitive, following live substitutions and
         *  ensuring every newly length-dependent persistent predicate is queued. */
        void mark_length_sensitive(const std::vector<BasicTerm>& terms);

        /**
         * @brief Get any predicate that has @p var on the right side (for inclusions) or input (for transducers) and save it to @p found_predicate
         * 
         * @return was such a predicate found?
         */
        bool get_predicate_with_var_on_right_side(const BasicTerm& var, Predicate& found_predicate) {
            for (const Predicate& inclusion : inclusions) {
                for (auto const& right_var : inclusion.get_right_set()) {
                    if (right_var == var) {
                        found_predicate = inclusion;
                        return true;
                    }
                }
            }
            for (const Predicate& transducer : transducers) {
                for (auto const& right_var : transducer.get_input()) {
                    if (right_var == var) {
                        found_predicate = transducer;
                        return true;
                    }
                }
            }
            return false;
        }

        /**
         * Check if the vector @p right_side_vars depends on @p left_side_vars, i.e. if some variable
         * (NOT literal) occuring in @p right_side_vars occurs also in @p left_side_vars
         */
        static bool is_dependent(const std::set<BasicTerm> &left_side_vars, const std::set<BasicTerm> &right_side_vars) {
            if (left_side_vars.empty()) {
                return false;
            }
            for (auto const &right_var : right_side_vars) {
                if (right_var.is_variable() && left_side_vars.contains(right_var)) {
                    return true;
                }
            }
            return false;
        }

        /**
         * @brief Substitutes variables from @p vars_to_substitute in predicates using substitution_map and removes unnnecessary nodes
         * 
         * Concretely, substitutes the variables of both sides of inclusions and vars in inputs/outputs of transducers,
         * both in the corresponding sets and in the worklist of predicates to process (if two nodes become equal, keeps only
         * one). Furthermore, it removes inclusions that have both sides equal after substitution.
         *
         * @return False if substitution exposes an infeasible equation.
         */
        bool substitute_vars(const std::set<BasicTerm>& vars_to_substitute);

        /**
         * @brief Get under-approximation of the postponed disequations length formula. For each disquation L != R add to 
         * the resulting conjunction a formula |L| != |R|.
         * 
         * @return LenNode Postponed disequations length under-approximation 
         */
        LenNode get_disequations_underapprox_length_formula() const;

        /**
         * @brief Collect vars that are referenced by constraints stored directly in this state
         *        (e.g., postponed disequality-length conjuncts and conversions) and therefore
         *        must not be fully removed from substitution-related structures.
         */
        std::set<BasicTerm> get_vars_referenced_by_state_constraints() const;

        /// @brief Remove vars @p vars_to_remove (except those in @p vars_to_keep ) from the subtitution_map/aut_ass
        void remove_vars(const std::set<BasicTerm>& vars_to_remove, const std::set<BasicTerm>& vars_to_keep);

        /**
         * @brief Get the length constraints for variable @p var
         * 
         * If @p var is substituted by x1x2x3... then it creates
         * |var| = |x1| + |x2| + |x3| + ... otherwise, if @p var
         * has an automaton assigned, it creates length constraint
         * representing all possible lengths of words in the automaton.
         */
        LenNode get_lengths(const BasicTerm& var) const;

        /**
         * @brief Flattens substitution_map so that each var maps only to vars in aut_assignment
         *
         * For example, if we have substitution_map[x] = yz, substitution_map[y] = z, and z is in aut_assignment, then at the end
         * we will have substitution_map[x] = zz and substitution_map[y] = z
         */
        void flatten_substition_map();

        /**
         * @brief Checks if @p var is substituted by empty word
         */
        bool is_var_empty_word(const BasicTerm& var) { return (substitution_map.count(var) > 0 && substitution_map.at(var).empty()); }

        /**
         * @brief Get the vector of variables substituting @p var.
         * 
         * In the case that @p var is not substituted (it is mapped to automaton), we return { @p var }.
         * Useful especially after calling flatten_subtitution_map().
         */
        std::vector<BasicTerm> get_substituted_vars(const BasicTerm& var) const {
            if (substitution_map.count(var) > 0)
                return substitution_map.at(var);
            else
                return std::vector<BasicTerm>{var};
        }

        /**
         * @brief Get the assigned automata of variables in a @p concatenation of variables.
         * 
         * If @p group_non_length is true, we also concatenate automata of the sequences of non-length variables.
         * A variable still receives its own division if it occurs on both sides of one inclusion or in
         * two inclusions that are not switched orientations of each other.
         * For example, for xyyxxzyz where y is length variable we will get 6 automata:
         *      - one for first x
         *      - second for first y
         *      - third for second y
         *      - fourth as a concatenation of automata for xxz
         *      - fifth for y
         *      - sixth for z
         * If @p group_non_length was false, we would get 8 automata, one for each variable.
         * 
         * Assumes that each variable in @p concatenation is assigned in aut_ass.
         * 
         * @return a pair where first item is the vector of automata and the second tells us for each automaton which variables were concatenated for it 
         */
        [[nodiscard]] std::pair<std::vector<std::shared_ptr<mata::nfa::Nfa>>,std::vector<std::vector<BasicTerm>>> get_automata_and_division_of_concatenation(const std::vector<BasicTerm>& concatenation, bool group_non_length);

        bool contains_length_var(const std::vector<BasicTerm>& vars) {
            for (const BasicTerm& var : vars) {
                if (length_sensitive_vars.contains(var)) {
                    return true;
                }
            }
            return false;
        }

        /**
         * @brief Adds a new fresh var whose name starts with @p var_prefix, is length-aware if @p is_length is true and assigned to automaton @p nfa.
         * 
         * If @p optimize_literal is true and @p nfa accepts exactly one word, the resulting variable will be literal corresponding to this word instead
         * and @p var_prefix and @p is_length are ignored. This assumes that @p nfa is trimmed and reduced (or determinized and minimized), otherwise
         * the test for @p nfa to aaccept one word can return false even if it accepts one word.
         * 
         * @return The newly created variable. 
         */
        BasicTerm add_fresh_var(std::shared_ptr<mata::nfa::Nfa> nfa, std::string var_prefix, bool is_length, bool optimize_literal);

        /**
         * @brief Replaces the dummy symbol in transducers by all symbols from @p replacements
         * 
         * If @p replacements is empty, it only deletes dummy symbols from transducers.
         */
        void replace_dummy_symbol_in_transducers_with(std::set<mata::Symbol> replacements);

        /**
         * @brief Replace disequality L != R with equalities while updating this solving state.
         *
         * The method updates this state (automata assignment and length-sensitive vars),
         * It stores created disequality-related length constraints into
         * disequations_len_formula_conjuncts and stores needed to_code
         * conversions in this state's conversions.
         *
         * @param diseq Disequality to replace.
         * @return Vector with created equalities.
         */
        std::vector<Predicate> replace_disequality(const Predicate& diseq);

        /**
         * @brief Expand postponed disequations into equations and enqueue them.
         *
         * Each postponed disequation is replaced by equations via replace_disequality().
         * The resulting equations are added to this state and also pushed for processing.
         */
        void translate_postponed_disequations_to_equations();

        /**
         * @brief Run lightweight preprocessing focused on postponed disequations and
         *        detect whether they are immediately unsatisfiable in this state.
         *
         * This method runs a local FormulaPreprocessor over `postponed_disequations`
         * using the current `aut_ass`, `length_sensitive_vars` and any conversion
         * variables. If the preprocessor detects immediate unsatisfiability it
         * returns `l_false` and does not change this state. Otherwise the method
         * persists the preprocessor's simplified disequations and the refined
         * automata/length information back into this `SolvingState` (it updates
         * `postponed_disequations`, `aut_ass` and inserts any discovered length
         * variables into `length_sensitive_vars`) and returns `l_true`.
         *
         * @return `l_false` iff preprocessing proves some disequation branch unsat,
         *         `l_true` otherwise.
         */
        lbool preprocess_disequations_for_unsat(const theory_str_noodler_params& params);

        std::string DOT_name = "init";
        std::string set_new_DOT_name() {
            static size_t DOT_name_counter = 0;
            DOT_name = std::string("SolvingState") + std::to_string(DOT_name_counter);
            ++DOT_name_counter;
            return DOT_name;
        }
        std::string print_to_DOT() const;
    };

    struct LocalNoodleResult {
        SolvingState state;
        std::set<BasicTerm> substituted_vars;
    };

    /** Process the local constraints generated by one raw noodle.  One noodle can
     *  materialize multiple children when a nullable overlap is accelerated. */
    std::vector<LocalNoodleResult> process_substituting_inclusions(
        SolvingState state,
        const std::vector<Predicate>& left_inclusions,
        const std::vector<Predicate>& right_inclusions,
        bool on_cycle,
        size_t parent_depth,
        bool enable_overlap_acceleration);
}

#endif
