#include <iostream>
#include <unordered_set>

#include <catch2/catch_test_macros.hpp>
#include <mata/nfa/nfa.hh>
#include <mata/nft/nft.hh>

#include "smt/theory_str_noodler/formula.h"

using namespace smt::noodler;


TEST_CASE( "Transducer predicate", "[noodler]" ) {

    // two-tape transducer by default
    mata::nft::Nft nft{2};
    nft.initial = {0};
    nft.final = {1};
    nft.insert_word_by_levels(0, { {'a'}, {'b'} } , 1);
    CHECK(nft.delta.num_of_states() == 3);
    CHECK(nft.is_in_lang_by_levels({ {'a'}, {'b'} }));

    BasicTerm x {BasicTermType::Variable, "x"};
    BasicTerm y {BasicTermType::Variable, "x"};

    SECTION("Switched predicate") {
         // transducer implementing inversion relation
        mata::nft::Nft nft_inv = mata::nft::invert_levels(nft);
        CHECK(nft_inv.is_in_lang_by_levels({ {'b'}, {'a'} }));
        CHECK(!nft_inv.is_in_lang_by_levels({ {'a'}, {'b'} }));

        Predicate pred_trans { PredicateType::Transducer, { { x }, { y } }, std::make_shared<mata::nft::Nft>(nft) };
        Predicate pred_trans_switch = pred_trans.get_switched_sides_predicate();

        // result
        Predicate switch_res { PredicateType::Transducer, { { y }, { x } }, std::make_shared<mata::nft::Nft>(nft_inv) };
        CHECK(pred_trans_switch.strong_equals(switch_res));
    }

    SECTION("Comparison") {
        mata::nft::Nft nft_other{2};
        nft_other.initial = {0};
        nft_other.final = {1};
        nft_other.insert_word_by_levels(0, { {'c'}, {'d'} } , 1);

        
        Predicate p1 { PredicateType::Transducer, { { x }, { y } }, std::make_shared<mata::nft::Nft>(nft) };
        Predicate p2 { PredicateType::Transducer, { { x }, { y } }, std::make_shared<mata::nft::Nft>(nft_other) };
        Predicate p3 { PredicateType::Transducer, { { x }, { y } }, p1.get_transducer() };
        CHECK(p1 != p2);
        CHECK(!(p1 < p1));
        CHECK(p1 == p1);
        CHECK(p1.strong_equals(p1));
        CHECK(p1.strong_equals(p3));
        CHECK(!(p1 < p3));
        CHECK(!(p3 < p1));

        std::set<Predicate> st{};
        st.insert(p1);
        st.insert(p2);
        st.insert(p3);
        CHECK(st.size() == 2);

        std::unordered_set<Predicate> st_un{};
        st_un.insert(p1);
        st_un.insert(p2);
        st_un.insert(p3);
        CHECK(st_un.size() == 2);
    }

    SECTION("Replace") {
        mata::nft::Nft nft_other{2};
        nft_other.initial = {0};
        nft_other.final = {1};
        nft_other.insert_word_by_levels(0, { {'c'}, {'d'} } , 1);
        auto nft_ptr = std::make_shared<mata::nft::Nft>(nft);

        
        Predicate p1 { PredicateType::Transducer, { { x }, { y } }, nft_ptr };
        Predicate pres { PredicateType::Transducer, { { x }, { x } }, nft_ptr };

        Formula f{};
        f.add_predicate(p1);
        f.replace({x}, {y});

        Formula fres {};
        fres.add_predicate(pres);
        CHECK(f == fres);
    }
}

TEST_CASE("Equation simplification splits at balanced boundaries", "[noodler]") {
    const BasicTerm A{BasicTermType::Variable, "A"};
    const BasicTerm B{BasicTermType::Variable, "B"};
    const BasicTerm C{BasicTermType::Variable, "C"};
    const BasicTerm D{BasicTermType::Variable, "D"};
    const BasicTerm E{BasicTermType::Variable, "E"};
    const BasicTerm F{BasicTermType::Variable, "F"};
    const BasicTerm X{BasicTermType::Variable, "X"};
    const BasicTerm Y{BasicTermType::Variable, "Y"};

    auto check_part = [](
            const Predicate::EquationSimplificationResult::EquationSides& part,
            const std::vector<BasicTerm>& expected_left,
            const std::vector<BasicTerm>& expected_right) {
        CHECK(part.left == expected_left);
        CHECK(part.right == expected_right);
    };

    SECTION("prefix splitting is repeated to a fixed point") {
        std::vector<BasicTerm> left{A, B, C, D, E, F};
        std::vector<BasicTerm> right{B, A, D, C, F, E};

        Predicate::EquationSimplificationResult result =
            Predicate::simplify_equation(left, right);

        CHECK(result.kind == Predicate::EquationSimplificationResult::Kind::NoConsequence);
        CHECK(left == std::vector<BasicTerm>({A, B}));
        CHECK(right == std::vector<BasicTerm>({B, A}));
        REQUIRE(result.split_equations.size() == 2);
        check_part(result.split_equations[0], {C, D}, {D, C});
        check_part(result.split_equations[1], {E, F}, {F, E});
    }

    SECTION("suffix splitting is repeated to a fixed point") {
        std::vector<BasicTerm> left{X, A, B, C, D};
        std::vector<BasicTerm> right{Y, B, A, D, C};

        Predicate::EquationSimplificationResult result =
            Predicate::simplify_equation(left, right);

        CHECK(result.kind == Predicate::EquationSimplificationResult::Kind::NoConsequence);
        CHECK(left == std::vector<BasicTerm>({X}));
        CHECK(right == std::vector<BasicTerm>({Y}));
        REQUIRE(result.split_equations.size() == 2);
        check_part(result.split_equations[0], {A, B}, {B, A});
        check_part(result.split_equations[1], {C, D}, {D, C});
    }

    SECTION("only one matching prefix needs to be proper") {
        std::vector<BasicTerm> left{A, B};
        std::vector<BasicTerm> right{B, A, C};

        Predicate::EquationSimplificationResult result =
            Predicate::simplify_equation(left, right);

        CHECK(result.kind == Predicate::EquationSimplificationResult::Kind::NoConsequence);
        CHECK(left == std::vector<BasicTerm>({A, B}));
        CHECK(right == std::vector<BasicTerm>({B, A}));
        REQUIRE(result.split_equations.size() == 1);
        check_part(result.split_equations[0], {}, {C});
    }

    SECTION("a split boundary may occur inside a literal") {
        const BasicTerm a{BasicTermType::Literal, "a"};
        const BasicTerm ab{BasicTermType::Literal, "ab"};
        const BasicTerm b{BasicTermType::Literal, "b"};
        std::vector<BasicTerm> left{A, ab, B, X};
        std::vector<BasicTerm> right{a, A, b, B, Y};

        Predicate::EquationSimplificationResult result =
            Predicate::simplify_equation(left, right);

        CHECK(result.kind == Predicate::EquationSimplificationResult::Kind::NoConsequence);
        CHECK(left == std::vector<BasicTerm>({A, a}));
        CHECK(right == std::vector<BasicTerm>({a, A}));
        REQUIRE(result.split_equations.size() == 1);
        check_part(result.split_equations[0], {X}, {Y});
    }

    SECTION("literal characters are compared by count at the split boundary") {
        const BasicTerm a{BasicTermType::Literal, "a"};
        const BasicTerm b{BasicTermType::Literal, "b"};
        std::vector<BasicTerm> left{a, A, X};
        std::vector<BasicTerm> right{b, A, Y};

        Predicate::EquationSimplificationResult result =
            Predicate::simplify_equation(left, right);

        CHECK(result.kind == Predicate::EquationSimplificationResult::Kind::Infeasible);
        CHECK(left == std::vector<BasicTerm>({a}));
        CHECK(right == std::vector<BasicTerm>({b}));
        CHECK(result.split_equations.empty());
    }

    SECTION("variable occurrences must match, not only the variable set") {
        std::vector<BasicTerm> left{A, A, B, X};
        std::vector<BasicTerm> right{B, A, B, Y};

        Predicate::EquationSimplificationResult result =
            Predicate::simplify_equation(left, right);

        CHECK(result.kind == Predicate::EquationSimplificationResult::Kind::NoConsequence);
        CHECK(result.split_equations.empty());
        CHECK(left == std::vector<BasicTerm>({A, A, B, X}));
        CHECK(right == std::vector<BasicTerm>({B, A, B, Y}));
    }
}
