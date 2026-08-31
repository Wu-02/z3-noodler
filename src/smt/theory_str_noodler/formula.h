/**
 * @brief Create basic representation of firnzkae.
 *
 * Each equation or inequation consists of a left and right side of the equation which hold a vector of basic equation
 *  terms.
 * Each term is of one of the following types:
 *     - Literal,
 *     - Variable, or
 *     - operation such as IndexOf, Length, etc.
 */

#ifndef Z3_NOODLER_FORMULA_H
#define Z3_NOODLER_FORMULA_H

#include <utility>
#include <vector>
#include <stdexcept>
#include <memory>
#include <cassert>
#include <unordered_map>
#include <string>
#include <string_view>
#include <set>
#include <map>
#include <unordered_set>
#include <iostream>
#include <mata/nft/nft.hh>

#include "util/zstring.h"
#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"

namespace smt::noodler {
    enum struct PredicateType {
        Equation,
        Inequation,
        NotContains,
        Transducer, 
    };

    [[nodiscard, maybe_unused]] static inline std::string to_string(PredicateType predicate_type) {
        switch (predicate_type) {
            case PredicateType::Equation:
                return "Equation";
            case PredicateType::Inequation:
                return "Inequation";
            case PredicateType::NotContains:
                return "Notcontains";
            case PredicateType::Transducer:
                return "Transducer";
        }

        throw std::runtime_error("Unhandled predicate type passed to to_string().");
    }

    enum struct BasicTermType {
        Variable, // string and int vars (for string vars we pretend it is its length in LenNode)
        RealVariable, // real variables (important for LenNode)
        Literal, // string literal
        Length, // numeral literal
    };

    [[nodiscard, maybe_unused]] static inline std::string to_string(BasicTermType term_type) {
        switch (term_type) {
            case BasicTermType::Variable:
                return "Variable";
            case BasicTermType::RealVariable:
                return "RealVariable";
            case BasicTermType::Literal:
                return "Literal";
            case BasicTermType::Length:
                return "Length";
        }

        throw std::runtime_error("Unhandled basic term type passed to to_string().");
    }

    class BasicTerm {
    public:
        explicit BasicTerm(BasicTermType type): type(type) {}
        BasicTerm(BasicTermType type, zstring name): type(type), name(std::move(name)) {}

        [[nodiscard]] BasicTermType get_type() const { return type; }
        [[nodiscard]] bool is_variable() const { return (type == BasicTermType::Variable || type == BasicTermType::RealVariable); }
        [[nodiscard]] bool is_real_variable() const { return type == BasicTermType::RealVariable; }
        [[nodiscard]] bool is_literal() const { return type == BasicTermType::Literal; }
        [[nodiscard]] bool is(BasicTermType term_type) const { return type == term_type; }

        [[nodiscard]] zstring get_name() const { return name; }
        void set_name(zstring new_name) { name = std::move(new_name); }

        [[nodiscard]] bool equals(const BasicTerm& other) const {
            return type == other.get_type() && name == other.get_name();
        }

        [[nodiscard]] std::string to_string() const;

        struct HashFunction {
            size_t operator() (const BasicTerm& basic_term) const {
                size_t row_hash = std::hash<BasicTermType>()(basic_term.type);
                size_t col_hash = basic_term.name.hash() << 1;
                return row_hash ^ col_hash;
            }
        };

    private:
        BasicTermType type;
        // name of the variable, or the given literal
        zstring name;
    }; // Class BasicTerm.

    [[nodiscard, maybe_unused]] static inline std::string to_string(const BasicTerm& basic_term) {
        return basic_term.to_string();
    }


    [[maybe_unused]] static inline std::ostream& operator<<(std::ostream& os, const BasicTerm& basic_term) {
        os << basic_term.to_string();
        return os;
    }

    static inline bool operator==(const BasicTerm& lhs, const BasicTerm& rhs) { return lhs.equals(rhs); }
    static inline bool operator!=(const BasicTerm& lhs, const BasicTerm& rhs) { return !(lhs == rhs); }
    static inline bool operator<(const BasicTerm& lhs, const BasicTerm& rhs) {
        if (lhs.get_type() < rhs.get_type()) {
            return true;
        } else if (lhs.get_type() > rhs.get_type()) {
            return false;
        }
        // Types are equal. Compare names.
        if (lhs.get_name() < rhs.get_name()) {
            return true;
        }
        return false;
    }
    static inline bool operator>(const BasicTerm& lhs, const BasicTerm& rhs) { return !(lhs < rhs); }

    [[nodiscard]] static std::string to_string(const std::vector<BasicTerm>& vec, const std::string& delimiter = " ") {
        if(vec.empty()) return "";
        std::string ret = vec[0].to_string();
        for(size_t i = 1; i < vec.size(); i++) {
            ret += delimiter + vec[i].to_string();
        }
        return ret;
    }

    [[maybe_unused]] static inline std::ostream& operator<<(std::ostream& os, const std::vector<BasicTerm>& vec) {
        os << to_string(vec);
        return os;
    }

    //----------------------------------------------------------------------------------------------------------------------------------

    /**
     * @brief Length formula precision
     */
    enum struct LenNodePrecision {
        PRECISE,
        UNDERAPPROX,
        OVERAPPROX,
    };

    /**
     * Given two precisions p0 and p1 of formulae for certain parts of the current SAT branch (e.g. only not-contains predicates), compute the precision of the result.
     * 
     * For example, we have: `not-contains(x, y) AND x != z`, where:
     *    - we (p0=)overapproximate the not-contains to {a, b, c, d} whereas the real set of models is {a, b}
     *    - we have (p1=)precise solutions of the disequation {a, c} (to the disequation)
     * So taking a conjunction of the overapproximation+precise formula for disequation, we have the resulting precision result=overapproximation as
     *  Models of the conjunction using approximations: {a, b, c, d} && {a, c} = {a, c}
     *  Models of the real formula, if we could compute it: {a, b} && {a, c} = {a}
     */
    LenNodePrecision get_resulting_precision_for_conjunction(const LenNodePrecision& p0, const LenNodePrecision& p1);

    enum struct LenFormulaType {
        PLUS,
        MINUS,
        TIMES,
        EQ,
        NEQ, // not equal
        NOT,
        LEQ, // <=
        LT, // <
        LEAF, // int or variable (use LenNode(int) or LenNode(BasicTerm) constructors)
        AND,
        OR,
        TRUE,
        FALSE,
        EXISTS, // existential quantifier
        FORALL, // quantifier for all
    };

    struct LenNode {
        LenFormulaType type;
        BasicTerm atom_val;
        std::vector<struct LenNode> succ;

        LenNode(rational k) : type(LenFormulaType::LEAF), atom_val(BasicTermType::Length, zstring(k)), succ() { };
        LenNode(int k) : LenNode(rational(k)) { };
        LenNode(unsigned k) : LenNode(rational(k)) { };
        LenNode(BasicTerm val) : type(LenFormulaType::LEAF), atom_val(val), succ() { };
        LenNode(LenFormulaType tp, std::vector<struct LenNode> s = {}) : type(tp), atom_val(BasicTerm(BasicTermType::Length)), succ(s) { };
    };

    static inline std::ostream& operator<<(std::ostream& os, const LenNode& node) {
        auto children_iterator = node.succ.begin(); // Some nodes, e.g., quantifiers would like to consume successor nodes
        bool was_opening_parenthesis_emitted = true;

        switch (node.type)
        {
        case LenFormulaType::TRUE:
            return (os << "true");
        case LenFormulaType::FALSE:
            return (os << "false");
        case LenFormulaType::LEAF: {
            zstring name = node.atom_val.get_name();
            if (node.atom_val.is(BasicTermType::Length)) {
                rational(name.encode().c_str()).display_smt2(os);
                return os;
            }
            return (os << node.atom_val.get_name());
        }
        case LenFormulaType::NOT:
            return os << "(not" << node.succ.at(0) << ")";
        case LenFormulaType::LEQ:
            return os << "(<= " << node.succ.at(0) << " " << node.succ.at(1) << ")";
        case LenFormulaType::LT:
            return os << "(< " << node.succ.at(0) << " " << node.succ.at(1) << ")";
        case LenFormulaType::EQ:
            return os << "(= " << node.succ.at(0) << " " << node.succ.at(1) << ")";
        case LenFormulaType::NEQ:
            return os << "(not (= " << node.succ.at(0) << " " << node.succ.at(1) << "))";
        case LenFormulaType::PLUS:
            if (node.succ.size() > 1) {
                os << "(+";
            } else {
                was_opening_parenthesis_emitted = false;
            }
            break;
        case LenFormulaType::MINUS:
            os << "(-";
            break;
        case LenFormulaType::TIMES:
            os << "(*";
            break;
        case LenFormulaType::AND:
            if (node.succ.size() > 1) {
                os << "(and";
            } else {
                was_opening_parenthesis_emitted = false;
            }
            break;
        case LenFormulaType::OR:
            if (node.succ.size() > 1) {
                os << "(or";
            } else {
                was_opening_parenthesis_emitted = false;
            }
            break;
        case LenFormulaType::FORALL: {
            const auto& quantified_var = *children_iterator;
            children_iterator++;

            os << "(forall (( " << quantified_var << " Int))";
            break;
        }
        case LenFormulaType::EXISTS: {
            const auto& quantified_var = *children_iterator;
            children_iterator++;
            os << "(exists (( " << quantified_var << " Int))";
            break;
        }
        default:
            UNREACHABLE();
        }

        for (; children_iterator != node.succ.end(); children_iterator++) {
            const auto& child = *children_iterator;
            os << " " << child;
        }

        if (was_opening_parenthesis_emitted) {
            os << ")";
        }
        return os;
    }
    /**
     * Recursively collect all free variables in the given formula.
     */
    std::set<BasicTerm> collect_free_vars(const LenNode& formula);

    /**
     * Write the given formula as SMT2 to the given @p out_stream, including preamble.
     */
    void write_len_formula_as_smt2(const LenNode& formula, std::ostream& out_stream);

    /**
     * Apply the given substitution. Variables are assumed to be named uniquely in the formula.
     */
    LenNode substitute_free_vars_for_concrete_values(const LenNode& formula, const std::map<BasicTerm, int> values);

} // namespace smt::noodler

namespace std {
    template<>
    struct hash<smt::noodler::BasicTerm> {
        inline size_t operator()(const smt::noodler::BasicTerm& basic_term) const {
            return smt::noodler::BasicTerm::HashFunction()(basic_term);
        }
    };
} // namespace std

namespace smt::noodler {

    //----------------------------------------------------------------------------------------------------------------------------------

    class Predicate {
    private:
        PredicateType type;
        std::vector<std::vector<BasicTerm>> params;
        // transducer for the case of PredicateType::Transducer where params[0] is input and params[1] is output
        std::shared_ptr<mata::nft::Nft> transducer = nullptr;
    public:
        enum struct EquationSideType { // can be used also for disequations
            Left,
            Right,
        };

        Predicate() : type(PredicateType::Equation) {}
        explicit Predicate(const PredicateType type): type(type), params(), transducer() {
            if (is_two_sided()) {
                params.resize(2);
                params.emplace_back();
                params.emplace_back();
            }
        }

        explicit Predicate(const PredicateType type, std::vector<std::vector<BasicTerm>> par): type(type), params(par), transducer() {
            assert(!is_two_sided() || params.size() == 2);
        }

        explicit Predicate(const PredicateType type, std::vector<std::vector<BasicTerm>> par, std::shared_ptr<mata::nft::Nft> trans) : 
            type(type),
            params(par),
            transducer(trans) {
            assert(type == PredicateType::Transducer);
            assert(trans->levels.num_of_levels == 2);
        }


        static Predicate create_equation(std::vector<BasicTerm> left_side, std::vector<BasicTerm> right_side) {
            return Predicate{PredicateType::Equation, {std::move(left_side), std::move(right_side)}};
        }

        static Predicate create_disequation(std::vector<BasicTerm> left_side, std::vector<BasicTerm> right_side) {
            return Predicate{PredicateType::Inequation, {std::move(left_side), std::move(right_side)}};
        }

        static Predicate create_transducer(std::shared_ptr<mata::nft::Nft> trans, std::vector<BasicTerm> input, std::vector<BasicTerm> output) {
            return Predicate{PredicateType::Transducer, {std::move(input), std::move(output)}, trans};
        }

        static Predicate create_not_contains(std::vector<BasicTerm> haystick, std::vector<BasicTerm> needle) {
            return Predicate{PredicateType::NotContains, {std::move(haystick), std::move(needle)}};
        }

        [[nodiscard]] PredicateType get_type() const { return type; }
        [[nodiscard]] bool is_equation() const { return type == PredicateType::Equation; }
        [[nodiscard]] bool is_inequation() const { return type == PredicateType::Inequation; }
        [[nodiscard]] bool is_not_cont() const { return type == PredicateType::NotContains; }
        [[nodiscard]] bool is_eq_or_ineq() const { return is_equation() || is_inequation(); }
        [[nodiscard]] bool is_transducer() const { return is(PredicateType::Transducer); }
        [[nodiscard]] bool is_two_sided() const { return is_equation() || is_inequation() || is_not_cont() || is_transducer(); }
        [[nodiscard]] bool is(const PredicateType predicate_type) const { return predicate_type == this->type; }

        [[nodiscard]] std::vector<std::vector<BasicTerm>>& get_params() { return this->params; }
        [[nodiscard]] const std::vector<std::vector<BasicTerm>>& get_params() const { return this->params; }

        /// get left side of (dis)equation 
        [[nodiscard]] std::vector<BasicTerm>& get_left_side() {
            assert(is_eq_or_ineq());
            return params[0];
        }

        /// get left side of (dis)equation 
        [[nodiscard]] const std::vector<BasicTerm>& get_left_side() const {
            assert(is_eq_or_ineq());
            return params[0];
        }

        /// get right side of (dis)equation 
        [[nodiscard]] std::vector<BasicTerm>& get_right_side() {
            assert(is_eq_or_ineq());
            return params[1];
        }

        /// get right side of (dis)equation 
        [[nodiscard]] const std::vector<BasicTerm>& get_right_side() const {
            assert(is_eq_or_ineq());
            return params[1];
        }

        /// set right side of (dis)equation 
        void set_left_side(const std::vector<BasicTerm> &new_left_side) {
            assert(is_eq_or_ineq());
            params[0] = new_left_side;
        }

        /// set left side of (dis)equation 
        void set_left_side(std::vector<BasicTerm> &&new_left_side) {
            assert(is_eq_or_ineq());
            params[0] = std::move(new_left_side);
        }

        /// set right side of (dis)equation 
        void set_right_side(const std::vector<BasicTerm> &new_right_side) {
            assert(is_eq_or_ineq());
            params[1] = new_right_side;
        }

        /// general get_param(int) for arbitrary predicate type
        [[nodiscard]] const std::vector<BasicTerm>& get_param(size_t param) const {
            return this->params[param];
        }

        /// set right side of (dis)equation 
        void set_right_side(std::vector<BasicTerm> &&new_right_side) {
            assert(is_eq_or_ineq());
            params[1] = std::move(new_right_side);
        }

        /// get input of transducer
        [[nodiscard]] std::vector<BasicTerm>& get_input() {
            assert(is_transducer());
            return params[0];
        }

        /// get input of transducer
        [[nodiscard]] const std::vector<BasicTerm>& get_input() const {
            assert(is_transducer());
            return params[0];
        }

        /// get output of transducer
        [[nodiscard]] std::vector<BasicTerm>& get_output() {
            assert(is_transducer());
            return params[1];
        }

        /// get output of transducer
        [[nodiscard]] const std::vector<BasicTerm>& get_output() const {
            assert(is_transducer());
            return params[1];
        }

        /// set input of transducer
        void set_input(const std::vector<BasicTerm> &new_input) {
            assert(is_transducer());
            params[0] = new_input;
        }

        /// set input of transducer
        void set_input(std::vector<BasicTerm> &&new_input) {
            assert(is_transducer());
            params[0] = std::move(new_input);
        }

        /// set output of transducer
        void set_output(const std::vector<BasicTerm> &new_output) {
            assert(is_transducer());
            params[1] = new_output;
        }

        /// set output of transducer
        void set_output(std::vector<BasicTerm> &&new_output) {
            assert(is_transducer());
            params[1] = std::move(new_output);
        }

        /// get haystack of notcontains
        [[nodiscard]] std::vector<BasicTerm>& get_haystack() {
            assert(is_not_cont());
            return params[0];
        }

        /// get haystack of notcontains
        [[nodiscard]] const std::vector<BasicTerm>& get_haystack() const {
            assert(is_not_cont());
            return params[0];
        }

        /// get needle of notcontains
        [[nodiscard]] std::vector<BasicTerm>& get_needle() {
            assert(is_not_cont());
            return params[1];
        }

        /// get needle of notcontains
        [[nodiscard]] const std::vector<BasicTerm>& get_needle() const {
            assert(is_not_cont());
            return params[1];
        }

        /// set haystack of transducer
        void set_haystack(const std::vector<BasicTerm> &new_haystack) {
            assert(is_not_cont());
            params[0] = new_haystack;
        }

        /// set haystack of transducer
        void set_haystack(std::vector<BasicTerm> &&new_haystack) {
            assert(is_not_cont());
            params[0] = std::move(new_haystack);
        }

        /// set needle of transducer
        void set_needle(const std::vector<BasicTerm> &new_needle) {
            assert(is_not_cont());
            params[1] = new_needle;
        }

        /// set needle of transducer
        void set_needle(std::vector<BasicTerm> &&new_needle) {
            assert(is_not_cont());
            params[1] = std::move(new_needle);
        }


        /// get set of all variables/literals occuring in the predicate
        [[nodiscard]] std::set<BasicTerm> get_set() const {
            std::set<BasicTerm> ret;
            for(const auto& side : this->params) {
                for(const BasicTerm& t : side)
                    ret.insert(t);
            }
            return ret;
        }

        /// get set of all variables/literals occuring in the paramater at @p index
        [[nodiscard]] std::set<BasicTerm> get_set_of_param(std::vector<std::vector<BasicTerm>>::size_type index) const {
            std::set<BasicTerm> ret;
            for(const BasicTerm& t : this->params[index]) {
                ret.insert(t);
            }
            return ret;
        }

        /// get set ofleft side variables/literals of (dis)equation 
        [[nodiscard]] std::set<BasicTerm> get_left_set() const {
            assert(is_eq_or_ineq());
            return get_set_of_param(0);
        }

        /// get set of right side variables/literals of (dis)equation 
        [[nodiscard]] std::set<BasicTerm> get_right_set() const {
            assert(is_eq_or_ineq());
            return get_set_of_param(1);
        }

        /// get set of input variables/literals of transducer
        [[nodiscard]] std::set<BasicTerm> get_input_set() const {
            assert(is_transducer());
            return get_set_of_param(0);
        }

        /// get set of output variables/literals of transducer
        [[nodiscard]] std::set<BasicTerm> get_output_set() const {
            assert(is_transducer());
            return get_set_of_param(1);
        }

        /// get set of haystack variables/literals of notcontains
        [[nodiscard]] std::set<BasicTerm> get_haystack_set() const {
            assert(is_not_cont());
            return get_set_of_param(0);
        }


        /// get set of needle variables/literals of notcontains
        [[nodiscard]] std::set<BasicTerm> get_needle_set() const {
            assert(is_not_cont());
            return get_set_of_param(1);
        }

        /// get set of only variables in the predicate
        [[nodiscard]] std::set<BasicTerm> get_vars() const;

        /// get set of only variables on @p side of (dis)equation
        [[nodiscard]] std::set<BasicTerm> get_side_vars(EquationSideType side) const;

        /**
         * @brief Check if the predicate contains only constant strings.
         */
        bool is_str_const() const {
            for(const auto& side : this->params) {
                for(const BasicTerm& t : side)
                    if(!t.is_literal()) return false;
            }
            return true;
        }

        /**
         * @brief Get the length formula of the (dis)equation.
         * For an equation X1 X2 ... Xn = Y1 Y2 ... Ym creates the formula
         * |X1|+|X2|+...+|Xn| = |Y1|+|Y2|+...+|Ym|
         * Similarly, for a disequation X1 X2 ... Xn != Y1 Y2 ... Ym creates the formula
         * |X1|+|X2|+...+|Xn| != |Y1|+|Y2|+...+|Ym|
         *
         * @return LenNode Root of the length formula
         */
        LenNode get_formula_eq() const {

            auto plus_chain = [&](const std::vector<BasicTerm>& side) {
                std::vector<LenNode> ops;
                if(side.size() == 0) {
                    return LenNode(BasicTerm(BasicTermType::Length, "0"));
                }
                if(side.size() == 1) {
                    return LenNode(side[0]);
                }
                for(const BasicTerm& t : side) {
                    LenNode n = LenNode(t);
                    ops.push_back(n);
                }
                return LenNode(LenFormulaType::PLUS, ops);
            };

            assert(is_eq_or_ineq());
            LenNode left = plus_chain(this->params[0]);
            LenNode right = plus_chain(this->params[1]);
            LenNode eq = LenNode(LenFormulaType::EQ, {left, right});

            if(is_inequation()) {
                eq =  LenNode(LenFormulaType::NOT, {eq});
            }

            return eq;
        }

        /// get @p side of (dis)equation 
        std::vector<BasicTerm>& get_side(EquationSideType side);

        /// get @p side of (dis)equation 
        [[nodiscard]] const std::vector<BasicTerm>& get_side(EquationSideType side) const;

        /// get predicate with switched sides (for (dis)equations and transducers), transducers also invert
        [[nodiscard]] Predicate get_switched_sides_predicate() const {
            assert(is_two_sided());
            // for transducers we need to invert tapes, i.e., T(x,y) iff T^{-1}(y,x)
            if(is_transducer()) {
                auto nft_inverse = std::make_shared<mata::nft::Nft>(mata::nft::invert_levels(*transducer));
                return Predicate::create_transducer(nft_inverse, get_output(), get_input());
            }
            return Predicate{ type, { get_right_side(), get_left_side() } };
        }

        /**
         * @brief Replace BasicTerm @p find in the given concatenation
         *
         * @param concat Concatenation to be searche/replaced
         * @param find  Find
         * @param replace Replace
         * @param res Result
         * @return Does the concatenation contain at least one occurrence of @p find ?
         */
        static bool replace_concat(
                const std::vector<BasicTerm>& concat,
                const std::vector<BasicTerm>& find,
                const std::vector<BasicTerm>& replace,
                std::vector<BasicTerm>& res) {
            bool modif = false;
            for(auto it = concat.begin(); it != concat.end(); ) {
                if(std::equal(it, it+find.size(), find.begin(), find.end())) {
                    res.insert(res.end(), replace.begin(), replace.end());
                    modif = true;
                    it += find.size();
                } else {
                    res.push_back(*it);
                    it++;
                }
            }
            return modif;
        }

        /**
         * @brief Term-by-term replacement: every element of @p concat equal to @p find is replaced
         *        by @p replacement. All results are appended to @p res.
         *
         * @return true if at least one replacement was made.
         */
        static bool replace_concat(
                std::vector<BasicTerm>& concat,
                const BasicTerm& find,
                const std::vector<BasicTerm>& replacement) {
            bool modif = false;
            std::vector<BasicTerm> res;
            for (const BasicTerm& t : concat) {
                if (t == find) {
                    res.insert(res.end(), replacement.begin(), replacement.end());
                    modif = true;
                } else {
                    res.push_back(t);
                }
            }
            if (modif) concat = std::move(res);
            return modif;
        }

        /**
         * @brief Term-by-term multi-substitution: every element of @p concat that is a key in
         *        @p subst_map is replaced by the corresponding value. Results are appended to @p res.
         *
         * @return true if at least one replacement was made.
         */
        static bool replace_concat(
                std::vector<BasicTerm>& concat,
                const std::unordered_map<BasicTerm, std::vector<BasicTerm>>& subst_map) {
            bool modif = false;
            std::vector<BasicTerm> res;
            for (const BasicTerm& t : concat) {
                auto it = subst_map.find(t);
                if (it != subst_map.end()) {
                    res.insert(res.end(), it->second.begin(), it->second.end());
                    modif = true;
                } else {
                    res.push_back(t);
                }
            }
            if (modif) concat = std::move(res);
            return modif;
        }

        // -----------------------------------------------------------------------
        // Simplification helpers (used by apply_subst and directly by callers)
        // -----------------------------------------------------------------------

        // Trim the common prefix of the two sides of an equation, supporting cross-length
        // literal splitting. E.g. ["abc", X] vs ["a", "bc", X] -> both become [X].
        // Stops silently on a literal mismatch (conservative; UNSAT detected later).
        static void reduce_front(std::vector<BasicTerm>& left, std::vector<BasicTerm>& right) {
            size_t li = 0, ri = 0;   // element indices
            size_t lo = 0, ro = 0;   // char offsets within current literal element

            while (li < left.size() && ri < right.size()) {
                const BasicTerm &l = left[li], &r = right[ri];
                bool l_is_lit = l.is_literal(), r_is_lit = r.is_literal();

                if (!l_is_lit && !r_is_lit) {
                    // Both non-literals: only cancel if they are the same variable.
                    if (l != r) break;
                    ++li; ++ri; lo = 0; ro = 0;
                } else if (l_is_lit && r_is_lit) {
                    const zstring &ls = l.get_name(), &rs = r.get_name();
                    unsigned llen = ls.length() - lo;
                    unsigned rlen = rs.length() - ro;
                    unsigned min_len = std::min(llen, rlen);
                    // Compare chars; stop silently on mismatch.
                    bool mismatch = false;
                    for (unsigned i = 0; i < min_len; ++i) {
                        if (ls[lo + i] != rs[ro + i]) { mismatch = true; break; }
                    }
                    if (mismatch) break;
                    if (llen == rlen) { ++li; ++ri; lo = 0; ro = 0; }
                    else if (llen < rlen) { ++li; lo = 0; ro += llen; }
                    else                 { ++ri; ro = 0; lo += rlen; }
                } else {
                    // One literal, one variable: cannot cancel.
                    break;
                }
            }

            // Rebuild left side from (li, lo) onwards.
            std::vector<BasicTerm> new_left, new_right;
            if (li < left.size()) {
                const BasicTerm &first = left[li];
                if (lo > 0 && first.is_literal()) {
                    zstring trimmed = first.get_name().extract(lo, first.get_name().length() - lo);
                    new_left.push_back(BasicTerm(BasicTermType::Literal, trimmed));
                    ++li;
                }
                new_left.insert(new_left.end(), left.begin() + li, left.end());
            }
            if (ri < right.size()) {
                const BasicTerm &first = right[ri];
                if (ro > 0 && first.is_literal()) {
                    zstring trimmed = first.get_name().extract(ro, first.get_name().length() - ro);
                    new_right.push_back(BasicTerm(BasicTermType::Literal, trimmed));
                    ++ri;
                }
                new_right.insert(new_right.end(), right.begin() + ri, right.end());
            }
            left  = std::move(new_left);
            right = std::move(new_right);
        };

        // Trim the common suffix of the two sides of an equation, supporting cross-length
        // literal splitting. Stops silently on a literal mismatch.
        static void reduce_back(std::vector<BasicTerm>& left, std::vector<BasicTerm>& right) {
            // lend/rend: exclusive upper bound of unconsumed region; lo/ro: chars consumed from back.
            size_t lend = left.size(), rend = right.size();
            size_t lo = 0, ro = 0;

            while (lend > 0 && rend > 0) {
                const BasicTerm &l = left[lend - 1], &r = right[rend - 1];
                bool l_is_lit = l.is_literal(), r_is_lit = r.is_literal();

                if (!l_is_lit && !r_is_lit) {
                    if (l != r) break;
                    --lend; --rend; lo = 0; ro = 0;
                } else if (l_is_lit && r_is_lit) {
                    const zstring &ls = l.get_name(), &rs = r.get_name();
                    unsigned llen = ls.length() - (unsigned)lo;
                    unsigned rlen = rs.length() - (unsigned)ro;
                    unsigned min_len = std::min(llen, rlen);
                    bool mismatch = false;
                    for (unsigned i = 0; i < min_len; ++i) {
                        if (ls[ls.length() - 1 - (unsigned)lo - i] != rs[rs.length() - 1 - (unsigned)ro - i]) {
                            mismatch = true; break;
                        }
                    }
                    if (mismatch) break;
                    if (llen == rlen) { --lend; --rend; lo = 0; ro = 0; }
                    else if (llen < rlen) { --lend; lo = 0; ro += llen; }
                    else                 { --rend; ro = 0; lo += rlen; }
                } else {
                    break;
                }
            }

            // Rebuild: keep left[0..lend-1], trimming lo chars from the back of left[lend-1] if needed.
            std::vector<BasicTerm> new_left(left.begin(), left.begin() + lend);
            if (lo > 0 && !new_left.empty() && new_left.back().is_literal()) {
                zstring trimmed = new_left.back().get_name().extract(0, new_left.back().get_name().length() - lo);
                new_left.back().set_name(trimmed);
            }
            std::vector<BasicTerm> new_right(right.begin(), right.begin() + rend);
            if (ro > 0 && !new_right.empty() && new_right.back().is_literal()) {
                zstring trimmed = new_right.back().get_name().extract(0, new_right.back().get_name().length() - ro);
                new_right.back().set_name(trimmed);
            }
            left  = std::move(new_left);
            right = std::move(new_right);
        };

        /// Merge consecutive literals in @p side into a single literal, e.g. ["a","bc",X] -> ["abc",X].
        static void merge_adjacent_literals(std::vector<BasicTerm>& side) {
            std::vector<BasicTerm> merged;
            for (const BasicTerm& t : side) {
                if (t.is_literal() && !merged.empty() && merged.back().is_literal()) {
                    merged.back().set_name(merged.back().get_name() + t.get_name());
                } else {
                    merged.push_back(t);
                }
            }
            side = std::move(merged);
        }

        struct EquationSimplificationResult {
            struct EquationSides {
                std::vector<BasicTerm> left;
                std::vector<BasicTerm> right;
            };

            enum class Kind {
                NoConsequence,
                EmptySideConsequence,
                Infeasible,
            };

            Kind kind = Kind::NoConsequence;
            std::vector<BasicTerm> residual;
            // simplify_equation keeps the first split part in its left/right arguments and
            // returns the remaining, logically equivalent conjuncts here.
            std::vector<EquationSides> split_equations;
        };

        /**
         * @brief Simplify an equation in place and derive either a necessary @c residual = epsilon
         *        length consequence or an infeasibility when its balanced literals differ.
         *
         * Prefix/suffix cancellation and literal merging rewrite the equation directly. In
         * addition, an equation is split whenever the prefixes on both sides, or the suffixes on
         * both sides, contain the same variable occurrences and the same total number of literal
         * characters, and at least one of the two parts is proper. A boundary may occur inside a
         * literal. Such parts always have equal length, so equality of the original words is
         * equivalent to equality of the two parts before the boundary and equality of the two
         * parts after it. Splitting is repeated on every resulting equation until no further
         * boundary is available.
         *
         * The first split equation is written back to @p left and @p right. The remaining
         * equivalent conjuncts are returned in @c split_equations and must replace the original
         * alongside the first equation.
         *
         * A returned empty-side equation captures only a length consequence, so it must be added
         * alongside the simplified split equations; otherwise word-order constraints are lost.
         * For example, A B = B A C splits into A B = B A and C = epsilon.
         *
         * The returned residual preserves the order of the surplus variables merely for stable
         * traces; its order has no semantic effect when compared with epsilon. A literal-symbol
         * surplus on one side requires a variable surplus on the other side. A one-sided,
         * non-zero literal-length balance is immediately infeasible.
        */
        static EquationSimplificationResult simplify_equation(
                std::vector<BasicTerm>& left, std::vector<BasicTerm>& right) {
            STRACE(str, tout << "Simplifying equation: " << left << " = " << right << std::endl;);
            using EquationSides = EquationSimplificationResult::EquationSides;
            using PartSummary = std::pair<std::map<BasicTerm, unsigned>, unsigned>;
            struct Boundary {
                // Number of whole terms before the boundary. A non-zero literal_offset places
                // the boundary that many characters into side[whole_terms].
                size_t whole_terms = 0;
                unsigned literal_offset = 0;
            };
            auto normalize = [](EquationSides& equation) {
                reduce_back(equation.left, equation.right);
                reduce_front(equation.left, equation.right);
                merge_adjacent_literals(equation.left);
                merge_adjacent_literals(equation.right);
            };

            auto advance_prefix = [](
                    const std::vector<BasicTerm>& side,
                    size_t& term_index,
                    unsigned& literal_offset,
                    PartSummary& summary,
                    Boundary& boundary) {
                while (term_index < side.size()) {
                    const BasicTerm& term = side[term_index];
                    if (term.is_variable()) {
                        ++summary.first[term];
                        ++term_index;
                        boundary = {term_index, 0};
                        return true;
                    }

                    SASSERT(term.is_literal());
                    const unsigned literal_length = term.get_name().length();
                    if (literal_offset < literal_length) {
                        ++literal_offset;
                        ++summary.second;
                        if (literal_offset == literal_length) {
                            ++term_index;
                            literal_offset = 0;
                            boundary = {term_index, 0};
                        } else {
                            boundary = {term_index, literal_offset};
                        }
                        return true;
                    }
                    ++term_index;
                }
                return false;
            };

            auto advance_suffix = [](
                    const std::vector<BasicTerm>& side,
                    size_t& term_end,
                    unsigned& literal_consumed,
                    PartSummary& summary,
                    Boundary& boundary) {
                while (term_end > 0) {
                    const size_t term_index = term_end - 1;
                    const BasicTerm& term = side[term_index];
                    if (term.is_variable()) {
                        ++summary.first[term];
                        --term_end;
                        boundary = {term_end, 0};
                        return true;
                    }

                    SASSERT(term.is_literal());
                    const unsigned literal_length = term.get_name().length();
                    if (literal_consumed < literal_length) {
                        ++literal_consumed;
                        ++summary.second;
                        const unsigned remaining = literal_length - literal_consumed;
                        boundary = {term_index, remaining};
                        if (remaining == 0) {
                            --term_end;
                            literal_consumed = 0;
                        }
                        return true;
                    }
                    --term_end;
                }
                return false;
            };

            auto split_side = [](const std::vector<BasicTerm>& side, Boundary boundary) {
                SASSERT(boundary.whole_terms <= side.size());
                std::vector<BasicTerm> prefix(
                    side.begin(), side.begin() + boundary.whole_terms);
                std::vector<BasicTerm> suffix;
                if (boundary.literal_offset == 0) {
                    suffix.assign(side.begin() + boundary.whole_terms, side.end());
                    return std::make_pair(std::move(prefix), std::move(suffix));
                }

                SASSERT(boundary.whole_terms < side.size());
                const BasicTerm& split_literal = side[boundary.whole_terms];
                SASSERT(split_literal.is_literal());
                const zstring literal = split_literal.get_name();
                SASSERT(boundary.literal_offset < literal.length());
                prefix.emplace_back(
                    BasicTermType::Literal,
                    literal.extract(0, boundary.literal_offset));
                suffix.emplace_back(
                    BasicTermType::Literal,
                    literal.extract(boundary.literal_offset, literal.length() - boundary.literal_offset));
                suffix.insert(
                    suffix.end(), side.begin() + boundary.whole_terms + 1, side.end());
                return std::make_pair(std::move(prefix), std::move(suffix));
            };

            auto is_proper_prefix = [](Boundary boundary, const std::vector<BasicTerm>& side) {
                return boundary.whole_terms < side.size();
            };

            auto is_proper_suffix = [](Boundary boundary) {
                return boundary.whole_terms != 0 || boundary.literal_offset != 0;
            };

            auto find_matching_prefixes = [&](
                    const EquationSides& equation,
                    Boundary& left_boundary,
                    Boundary& right_boundary) {
                size_t left_term = 0;
                size_t right_term = 0;
                unsigned left_literal_offset = 0;
                unsigned right_literal_offset = 0;
                PartSummary left_summary;
                PartSummary right_summary;
                while (advance_prefix(
                           equation.left,
                           left_term,
                           left_literal_offset,
                           left_summary,
                           left_boundary)
                       && advance_prefix(
                           equation.right,
                           right_term,
                           right_literal_offset,
                           right_summary,
                           right_boundary)) {
                    if (left_summary == right_summary
                            && (is_proper_prefix(left_boundary, equation.left)
                                || is_proper_prefix(right_boundary, equation.right))) {
                        return true;
                    }
                }
                return false;
            };

            auto find_matching_suffixes = [&](
                    const EquationSides& equation,
                    Boundary& left_boundary,
                    Boundary& right_boundary) {
                size_t left_term_end = equation.left.size();
                size_t right_term_end = equation.right.size();
                unsigned left_literal_consumed = 0;
                unsigned right_literal_consumed = 0;
                PartSummary left_summary;
                PartSummary right_summary;
                while (advance_suffix(
                           equation.left,
                           left_term_end,
                           left_literal_consumed,
                           left_summary,
                           left_boundary)
                       && advance_suffix(
                           equation.right,
                           right_term_end,
                           right_literal_consumed,
                           right_summary,
                           right_boundary)) {
                    if (left_summary == right_summary
                            && (is_proper_suffix(left_boundary)
                                || is_proper_suffix(right_boundary))) {
                        return true;
                    }
                }
                return false;
            };

            auto analyze_equation = [](const EquationSides& equation) {
                EquationSimplificationResult analysis;

                // An existing empty side already represents this consequence directly.
                if (equation.left.empty() || equation.right.empty()) return analysis;

                std::map<BasicTerm, int> variable_balance;
                int literal_length_balance = 0;
                std::map<unsigned, int> literal_symbol_balance;

                auto add_side = [&](const std::vector<BasicTerm>& side, int sign) {
                    for (const BasicTerm& term : side) {
                        if (term.is_variable()) {
                            variable_balance[term] += sign;
                        } else {
                            const zstring literal = term.get_name();
                            literal_length_balance += sign * static_cast<int>(literal.length());
                            for (unsigned i = 0; i < literal.length(); ++i) {
                                literal_symbol_balance[literal[i]] += sign;
                            }
                        }
                    }
                };
                add_side(equation.left, 1);
                add_side(equation.right, -1);

                bool all_nonnegative = literal_length_balance >= 0;
                bool all_nonpositive = literal_length_balance <= 0;
                bool has_surplus = literal_length_balance != 0;
                bool has_left_variable_surplus = false;
                bool has_right_variable_surplus = false;
                for (const auto& [term, balance] : variable_balance) {
                    (void)term;
                    all_nonnegative = all_nonnegative && balance >= 0;
                    all_nonpositive = all_nonpositive && balance <= 0;
                    has_surplus = has_surplus || balance != 0;
                    has_left_variable_surplus = has_left_variable_surplus || balance > 0;
                    has_right_variable_surplus = has_right_variable_surplus || balance < 0;
                }

                for (const auto& [symbol, balance] : literal_symbol_balance) {
                    (void)symbol;
                    if ((balance > 0 && !has_right_variable_surplus)
                        || (balance < 0 && !has_left_variable_surplus)) {
                        analysis.kind = EquationSimplificationResult::Kind::Infeasible;
                        return analysis;
                    }
                }
                if (!has_surplus) return analysis;
                if (!all_nonnegative && !all_nonpositive) return analysis;
                if (literal_length_balance != 0) {
                    analysis.kind = EquationSimplificationResult::Kind::Infeasible;
                    return analysis;
                }

                const bool surplus_on_left = all_nonnegative;
                const std::vector<BasicTerm>& surplus_side =
                    surplus_on_left ? equation.left : equation.right;
                std::map<BasicTerm, unsigned> remaining_variables;
                for (const auto& [term, balance] : variable_balance) {
                    if ((surplus_on_left && balance > 0) || (!surplus_on_left && balance < 0)) {
                        remaining_variables[term] =
                            static_cast<unsigned>(surplus_on_left ? balance : -balance);
                    }
                }

                for (const BasicTerm& term : surplus_side) {
                    if (!term.is_variable()) continue;
                    auto it = remaining_variables.find(term);
                    if (it != remaining_variables.end() && it->second > 0) {
                        analysis.residual.push_back(term);
                        --it->second;
                    }
                }

                for (const auto& [term, count] : remaining_variables) {
                    (void)term;
                    SASSERT(count == 0);
                }
                SASSERT(!analysis.residual.empty());
                analysis.kind = EquationSimplificationResult::Kind::EmptySideConsequence;
                return analysis;
            };

            // Keep splitting every produced part. A split strictly reduces the total number of
            // variables and literal characters in each child, because the full/full boundary is
            // deliberately excluded.
            std::vector<EquationSides> pending{{left, right}};
            std::vector<EquationSides> simplified_equations;
            bool was_split = false;
            while (!pending.empty()) {
                EquationSides equation = std::move(pending.back());
                pending.pop_back();
                normalize(equation);

                EquationSimplificationResult early_analysis = analyze_equation(equation);
                if (early_analysis.kind == EquationSimplificationResult::Kind::Infeasible) {
                    left = std::move(equation.left);
                    right = std::move(equation.right);
                    return early_analysis;
                }

                Boundary left_boundary;
                Boundary right_boundary;
                bool split = find_matching_prefixes(
                    equation, left_boundary, right_boundary);
                if (split) {
                    auto [left_prefix, left_suffix] = split_side(equation.left, left_boundary);
                    auto [right_prefix, right_suffix] = split_side(equation.right, right_boundary);
                    pending.push_back({std::move(left_suffix), std::move(right_suffix)});
                    pending.push_back({std::move(left_prefix), std::move(right_prefix)});
                    was_split = true;
                }
                if (split) continue;

                split = find_matching_suffixes(equation, left_boundary, right_boundary);
                if (split) {
                    auto [left_prefix, left_suffix] = split_side(equation.left, left_boundary);
                    auto [right_prefix, right_suffix] = split_side(equation.right, right_boundary);
                    pending.push_back({std::move(left_suffix), std::move(right_suffix)});
                    pending.push_back({std::move(left_prefix), std::move(right_prefix)});
                    was_split = true;
                }
                if (!split) simplified_equations.push_back(std::move(equation));
            }

            SASSERT(!simplified_equations.empty());
            left = std::move(simplified_equations.front().left);
            right = std::move(simplified_equations.front().right);

            EquationSimplificationResult result;
            result.split_equations.reserve(simplified_equations.size() - 1);
            for (size_t i = 1; i < simplified_equations.size(); ++i) {
                result.split_equations.push_back(std::move(simplified_equations[i]));
            }
            if (was_split) {
                STRACE(str, tout << "Split equation into "
                    << result.split_equations.size() + 1 << " parts" << std::endl;);
            }

            std::vector<EquationSides> equations_to_analyze{{left, right}};
            equations_to_analyze.insert(
                equations_to_analyze.end(), result.split_equations.begin(), result.split_equations.end());
            for (const EquationSides& equation : equations_to_analyze) {
                EquationSimplificationResult analysis = analyze_equation(equation);
                if (analysis.kind == EquationSimplificationResult::Kind::Infeasible) {
                    result.kind = EquationSimplificationResult::Kind::Infeasible;
                    result.residual.clear();
                    return result;
                }
                if (analysis.kind == EquationSimplificationResult::Kind::EmptySideConsequence) {
                    SASSERT(result.kind == EquationSimplificationResult::Kind::NoConsequence);
                    result.kind = EquationSimplificationResult::Kind::EmptySideConsequence;
                    result.residual = std::move(analysis.residual);
                }
            }

            if (result.kind == EquationSimplificationResult::Kind::EmptySideConsequence) {
                STRACE(str, tout << "Derived empty-side residual: "
                    << result.residual << " = []" << std::endl;);
            }
            return result;
        }

        /**
         * @brief Single-term substitution: replace every occurrence of @p find with
         *        @p replacement in both sides, then run reduce_back, reduce_front,
         *        and merge_adjacent_literals. Returns a consequence or infeasibility.
         */
        static EquationSimplificationResult apply_subst_eq(
                const BasicTerm& find,
                const std::vector<BasicTerm>& replacement,
                std::vector<BasicTerm>& left,
                std::vector<BasicTerm>& right) {
            for (std::vector<BasicTerm>& param : { std::ref(left), std::ref(right) }) {
                replace_concat(param, find, replacement);
            }
            STRACE(str, tout << "Before substitution: " << left << " = " << right << std::endl;);
            auto consequence = simplify_equation(left, right);
            STRACE(str, tout << "After simplification: " << left << " = " << right << std::endl;);
            return consequence;
        }

        /**
         * @brief In-place multi-variable substitution: simultaneously replace every term that is
         *        a key in @p subst_map with the corresponding value.  For equations, also runs
         *        reduce_back, reduce_front, and merge_adjacent_literals. Returns a consequence
         *        or infeasibility.
         */
        EquationSimplificationResult apply_subst(
                const std::unordered_map<BasicTerm, std::vector<BasicTerm>>& subst_map) {
            for (auto& param : params) {
                replace_concat(param, subst_map);
            }
            if (is_equation()) {
                return simplify_equation(params[0], params[1]);
            }
            return {};
        }

        /**
         * @brief Replace BasicTerm @p find in the predicate (do not modify the current one).
         *
         * @param find Find
         * @param replace Replace
         * @param res Where to store the modified predicate
         * @return Does the predicate contain at least one occurrence of @p find ?
         */
        bool replace(const std::vector<BasicTerm>& find, const std::vector<BasicTerm>& replace, Predicate& res) const {
            std::vector<std::vector<BasicTerm>> new_params;
            bool modif = false;
            for(const std::vector<BasicTerm>& p : this->params) {
                std::vector<BasicTerm> res_vec;
                bool r = Predicate::replace_concat(p, find, replace, res_vec);
                new_params.push_back(res_vec);
                modif = modif || r;
            }
            res = Predicate(this->type, new_params);
            res.transducer = this->transducer;
            return modif;
        }

        /**
         * Decide whether the @p side contains multiple occurrences of a single variable (with a same name).
         * 
         * @param side Side to check.
         * @return True if there are multiple occurrences of a single variable. False otherwise.
         */
        [[nodiscard]] bool mult_occurr_var_side(EquationSideType side) const;

        void replace(void* replace_map) {
            (void) replace_map;
            throw std::runtime_error("unimplemented");
        }

        void remove(void* terms_to_remove) {
            (void) terms_to_remove;
            throw std::runtime_error("unimplemented");
        }

        /**
         * @brief Count number of variables and sum of lengths of all literals
         * (represented by literal "" in the map).
         *
         * @param side Side of the term
         * @return std::map<BasicTerm, unsigned> Number of variables / sum of lits lengths
         */
        std::map<BasicTerm, unsigned> variable_count(const Predicate::EquationSideType side) const;

        /**
         * @brief Split literals into literals consisting of a single symbol.
         *
         * @return Predicate Modified predicate where each literal is a symbol.
         */
        Predicate split_literals() const;

        /**
         * @brief Strong equality. For the case of transducer predicates the transducers
         * are compared for identity (not just the indentity of pointers).
         * 
         * @param other Other predicate
         * @return true Is strongly equal
         */
        bool strong_equals(const Predicate& other) const;

        bool operator==(const Predicate& other) const {
            return (type == other.type && params == other.params && transducer == other.transducer);
        }

        std::strong_ordering operator<=>(const Predicate& other) const {
            if (type < other.type) {
                return std::strong_ordering::less;
            } else if (type > other.type) {
                return std::strong_ordering::greater;
            }
    
            // Types are equal. Compare data.
            if (params < other.params) {
                return std::strong_ordering::less;
            } else if (params > other.params) {
                return std::strong_ordering::greater;
            }

            if (transducer < other.transducer) {
                return std::strong_ordering::less;
            } else if (transducer > other.transducer) {
                return std::strong_ordering::greater;
            }

            return std::strong_ordering::equal;
        }

        [[nodiscard]] std::string to_string() const;

        /** Convert predicate to SMT-LIB2 S-expression format for trace output */
        [[nodiscard]] std::string to_smt2() const;

        struct HashFunction {
            size_t operator()(const Predicate& predicate) const {
                size_t res{};
                size_t row_hash = std::hash<PredicateType>()(predicate.type);
                for(const auto& pr : predicate.get_params()) {
                    for(const BasicTerm& term : pr) {
                        size_t col_hash = BasicTerm::HashFunction()(term) << 1;
                        res ^= col_hash;
                    }
                }
                return row_hash ^ res;
            }
        };

        /**
         * @brief Get the transducer shared pointer (for the transducer predicates only).
         * 
         * @return std::shared_ptr<mata::nft::Nft> Transducer
         */
        const std::shared_ptr<mata::nft::Nft>& get_transducer() const {
            assert(is_transducer());
            return transducer;
        }
        std::shared_ptr<mata::nft::Nft>& get_transducer() {
            assert(is_transducer());
            return transducer;
        }
    }; // Class Predicate.

    [[nodiscard, maybe_unused]] static inline std::string to_string(const Predicate& predicate) {
        return predicate.to_string();
    }

    [[maybe_unused]] static inline std::ostream& operator<<(std::ostream& os, const Predicate& predicate) {
        os << predicate.to_string();
        return os;
    }

    //----------------------------------------------------------------------------------------------------------------------------------

    class Formula {
    private:
        std::vector<Predicate> predicates;
    public:
        std::vector<Predicate>& get_predicates() { return predicates; }
        const std::vector<Predicate>& get_predicates() const { return predicates; }

        // TODO: Use std::move for both add functions?
        void add_predicate(Predicate predicate) { predicates.push_back(std::move(predicate)); }

        std::string to_string() const {
            std::string ret;
            for(const Predicate& p : this->predicates) {
                ret += p.to_string() + "\n";
            }
            return ret;
        }

        /**
         * @brief Extract and remove predicate of the type @p type from the formula.
         * The predicates of the type @p type are stored in the output @p extracted
         * It removes the extracted predicates from the current formula.
         *
         * @param type Predicate type
         * @param[out] extracted Where to store extracted predicates
         */
        void extract_predicates(PredicateType type, Formula& extracted) {
            std::vector<Predicate> new_predicates {};
            for(const Predicate& pred : this->predicates) {
                if(pred.get_type() == type) {
                    extracted.add_predicate(pred);
                } else {
                    new_predicates.emplace_back(pred);
                }
            }
            this->predicates = new_predicates;
        }

        /**
         * @brief Does the Formula contain a predicate of a type @p type ?
         *
         * @param type Type of the predicate.
         * @return true <-> Formula contains predicate of type @p type.
         */
        bool contains_pred_type(PredicateType type) const {
            for(const Predicate& pred : this->predicates) {
                if(pred.get_type() == type) {
                    return true;
                }
            }
            return false;
        }

        /**
         * @brief Get union of variables from all predicates
         *
         * @return std::set<BasicTerm> Variables
         */
        std::set<BasicTerm> get_vars() const {
            std::set<BasicTerm> ret;
            for(const auto& p : this->predicates) {
                auto vars = p.get_vars();
                ret.insert(vars.begin(), vars.end());
            }
            return ret;
        }

        /**
         * @brief Check whether a formula is quadratic.
         *
         * @return true <-> quadratic
         */
        bool is_quadratic() const {
            std::map<BasicTerm, unsigned> occur_map;

            auto upd = [&occur_map] (const std::vector<BasicTerm>& vc) {
                for(const BasicTerm& bt : vc) {
                    if(!bt.is_variable()) continue;
                    occur_map[bt]++;
                }
            };
            for(const Predicate& pred : this->predicates) {
                if(!pred.is_equation()) {
                    return false;
                }
                upd(pred.get_right_side());
                upd(pred.get_left_side());
            }
            for(const auto& pr : occur_map) {
                if(pr.second > 2)
                    return false;
            }
            return true;
        }

        /**
         * @brief Check whether all predicates match the given type.
         *
         * @param tp Predicate type
         * @return true <-> All predicates are of type @p tp
         */
        bool all_of_type(PredicateType tp) {
            for(const Predicate& pred : this->predicates) {
                if(pred.get_type() != tp) {
                    return false;
                }
            }
            return true;
        }

        /**
         * @brief Replace in all predicates
         *
         * @param find What to find
         * @param replace What to replace
         * @return Formula Modified formula according to the replace
         */
        Formula replace(const std::vector<BasicTerm>& find, const std::vector<BasicTerm>& replace) const {
            Formula ret;
            for(const Predicate& pred : this->predicates) {
                Predicate res;
                pred.replace(find, replace, res);
                ret.add_predicate(res);
            }
            return ret;
        }

        /**
         * @brief Split literals into literals consisting of a single symbol.
         *
         * @return Formula Modified formula where each literal is a symbol.
         */
        Formula split_literals() const {
            Formula new_formula;
            for(const Predicate& pred : this->predicates) {
                new_formula.add_predicate(pred.split_literals());
            }
            return new_formula;
        }
    }; // Class Formula.

    [[nodiscard]] static inline bool operator==(const Formula& lhs, const Formula& rhs) { return lhs.get_predicates() == rhs.get_predicates(); }
    [[nodiscard, maybe_unused]] static inline bool operator!=(const Formula& lhs, const Formula& rhs) { return !(lhs == rhs); }
    [[nodiscard]] static inline bool operator<(const Formula& lhs, const Formula& rhs) {
       return lhs.get_predicates() < rhs.get_predicates();
    }
    [[nodiscard, maybe_unused]] static inline bool operator>(const Formula& lhs, const Formula& rhs) { return !(lhs < rhs); }

    // Conversions of strings to ints/code values and vice versa
    enum class ConversionType {
        TO_CODE,
        FROM_CODE,
        TO_INT,
        FROM_INT,
        TO_REAL,
        FROM_REAL
    };

    // Term conversion: to_int/from_int/to_code/from_code/to_real/from_real
    struct TermConversion {
        ConversionType type;
        BasicTerm string_var;
        BasicTerm number_var;

        rational width = rational(0); // maximum number of decimal places for FROM_REAL operation

        TermConversion(ConversionType type, BasicTerm string_var, BasicTerm number_var) : type(type), string_var(std::move(string_var)), number_var(std::move(number_var)) {}
        TermConversion(ConversionType type, BasicTerm string_var, BasicTerm number_var, rational width) : type(type), string_var(std::move(string_var)), number_var(std::move(number_var)), width(width) { SASSERT(type == ConversionType::FROM_REAL); }

        bool is_code_conversion() const { return (type == ConversionType::TO_CODE || type == ConversionType::FROM_CODE); }
        bool is_int_conversion() const { return (type == ConversionType::TO_INT || type == ConversionType::FROM_INT); }
        bool is_real_conversion() const { return (type == ConversionType::TO_REAL || type == ConversionType::FROM_REAL); }
    };

    inline std::string get_conversion_name(ConversionType type) {
        switch (type)
        {
        case ConversionType::TO_CODE:
            return "to_code";
        case ConversionType::FROM_CODE:
            return "from_code";
        case ConversionType::TO_INT:
            return "to_int";
        case ConversionType::FROM_INT:
            return "from_int";
        case ConversionType::TO_REAL:
            return "to_real";
        case ConversionType::FROM_REAL:
            return "from_real";

        default:
            UNREACHABLE();
            return "";
        }
    }

    /** Get SMT-LIB2 function name for a conversion type (e.g. "str.to_int") */
    inline std::string get_conversion_smt2_name(ConversionType type) {
        switch (type) {
        case ConversionType::TO_CODE:    return "str.to_code";
        case ConversionType::FROM_CODE:  return "str.from_code";
        case ConversionType::TO_INT:     return "str.to_int";
        case ConversionType::FROM_INT:   return "str.from_int";
        case ConversionType::TO_REAL:    return "str.to_real";
        case ConversionType::FROM_REAL:  return "str.from_real";
        default: UNREACHABLE(); return "";
        }
    }

    /**
     * Context (other formulae) in which a formula is to be used.
     */
    struct LenFormulaContext {
        ast_manager& manager;
        arith_util&  arith_utilities;
        seq_util  &  seq_utilities;

        /**
         * Maps quantified variable names to the quantifier-depth of the corresponding quantifier.
         *
         * Necessary to correctly compute de Brujin sequences for the indices, which facilitate
         * the binding between a quantifier and a new variable.
         */
        std::map<std::string, unsigned>& quantified_vars;
        std::map<BasicTerm, expr_ref>&   known_z3_exprs;

        int current_quantif_depth = 0;  // To compute de Brujin numbers for quantified variables
    };

    /**
     * Convert given len_node into z3's expression.
     * 
     * The function accepts a context (collections of references to managers/utils) to allow
     * for easier unit testing. If embedded in theory_str_noodler, one would have to instantiate
     * and setup a lot of things just to check whether a formula instance is being correctly converted.
     * 
     * @note: The function does not correctly handle nested quantifiers when variables have the same names.
     * 
     * @param ctx Collection of references to managers and utils used during the conversion.
     */
    expr_ref convert_len_node_to_z3_formula(LenFormulaContext &ctx, const LenNode &node);

    /**
     * Helper function to construct quantifier expressions when converting len_nodes into z3's expressions.
     */
    expr_ref construct_z3_expr_for_len_node_quantifier(LenFormulaContext& ctx, const LenNode& node, enum quantifier_kind quantif_kind);


} // Namespace smt::noodler.

namespace std {
    template<>
    struct hash<smt::noodler::Predicate> {
        inline size_t operator()(const smt::noodler::Predicate& predicate) const {
            size_t accum = smt::noodler::Predicate::HashFunction()(predicate);
            return accum;
        }
    };
}

#endif //Z3_NOODLER_FORMULA_H
