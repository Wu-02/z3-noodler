#include <iostream>
#include <algorithm>
#include <utility>

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers_exception.hpp>

#include "smt/theory_str_noodler/decision_procedure.h"
#include "smt/theory_str_noodler/theory_str_noodler.h"
#include "ast/reg_decl_plugins.h"
#include "test_utils.h"

TEST_CASE("mk_literal bridges rewritten Boolean expressions", "[noodler]") {
    smt_params params;
    ast_manager ast_m;
    reg_decl_plugins(ast_m);
    smt::context ctx{ast_m, params};
    theory_str_noodler_params noodler_params{};
    TheoryStrNoodlerCUT noodler{ctx, ast_m, noodler_params};
    auto& str = noodler.m_util_s.str;

    expr_ref suffix(ast_m.mk_fresh_const("suffix", str.mk_string_sort()), ast_m);
    expr_ref nonempty(str.mk_concat(str.mk_string(">"), suffix), ast_m);
    expr_ref impossible(ast_m.mk_eq(nonempty, str.mk_string("")), ast_m);

    SECTION("bridge a rewrite to false") {
        ctx.internalize(impossible, false);
        smt::literal original_literal = ctx.get_literal(impossible);
        REQUIRE(original_literal != smt::false_literal);
        ctx.assign(original_literal, smt::b_justification::mk_axiom());
        REQUIRE_FALSE(ctx.inconsistent());

        CHECK(noodler.mk_literal(impossible) == smt::false_literal);
        CHECK(ctx.inconsistent());
    }

    SECTION("bridge a rewrite to true") {
        expr_ref valid(ast_m.mk_not(impossible), ast_m);
        ctx.internalize(valid, false);
        smt::literal original_literal = ctx.get_literal(valid);
        REQUIRE(original_literal != smt::true_literal);
        ctx.assign(~original_literal, smt::b_justification::mk_axiom());
        REQUIRE_FALSE(ctx.inconsistent());

        CHECK(noodler.mk_literal(valid) == smt::true_literal);
        CHECK(ctx.inconsistent());
    }

    SECTION("do not internalize an unseen original expression") {
        REQUIRE_FALSE(ctx.lit_internalized(impossible));
        CHECK(noodler.mk_literal(impossible) == smt::false_literal);
        CHECK_FALSE(ctx.lit_internalized(impossible));
        CHECK_FALSE(ctx.inconsistent());
    }
}

TEST_CASE("Decision Procedure", "[noodler]") {
    smt_params params;
    ast_manager ast_m;
    reg_decl_plugins(ast_m);
    smt::context ctx{ast_m, params };
    theory_str_noodler_params noodler_params{};
    TheoryStrNoodlerCUT noodler{ ctx, ast_m, noodler_params };
    auto& m_util_s{ noodler.m_util_s };
    auto& m_util_a{ noodler.m_util_a };
    auto& m{ noodler.m };

    mata::nft::Nft identity{1, {0}, {0}};
    identity.add_transition(0, {'a', 'a'}, 0);
    identity.add_transition(0, {'b', 'b'}, 0);

    mata::nft::Nft transform_to_empty{1, {0}, {0}};
    transform_to_empty.add_transition(0, {'a', mata::nft::EPSILON}, 0);
    transform_to_empty.add_transition(0, {'b', mata::nft::EPSILON}, 0);

    AutAssignment init_ass;
    init_ass.set_alphabet({'a', 'b'});

    SECTION("unsat-simple", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        init_ass[get_var('x')] = regex_to_nfa("a");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("b");
        init_ass[get_var('u')] = regex_to_nfa("b*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("sat-simple", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("a*");
        init_ass[get_var('u')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_true);
    }

    SECTION("unsat-FM-example", "[noodler]") {

        Formula equalities;
        equalities.add_predicate(create_equality("zyx", "xxz"));
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("a+b+");
        init_ass[get_var('z')] = regex_to_nfa("b*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("unsat-simple-length", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        init_ass[get_var('x')] = regex_to_nfa("a");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("b");
        init_ass[get_var('u')] = regex_to_nfa("b*");
        DecisionProcedureCUT proc(equalities, init_ass, { BasicTerm(BasicTermType::Variable, "x"), BasicTerm(BasicTermType::Variable, "z") }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("sat-simple-length", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("a*");
        init_ass[get_var('u')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { BasicTerm(BasicTermType::Variable, "x"), BasicTerm(BasicTermType::Variable, "z") }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution());
        CHECK(proc.compute_next_solution());
        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("sat-simple-length-substitution", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        init_ass[get_var('x')] = regex_to_nfa("a");
        init_ass[get_var('y')] = regex_to_nfa("ab*");
        init_ass[get_var('z')] = regex_to_nfa("ab*");
        init_ass[get_var('u')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { BasicTerm(BasicTermType::Variable, "x"), BasicTerm(BasicTermType::Variable, "z") }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();

        REQUIRE(proc.compute_next_solution() == lbool::l_true);

        REQUIRE(proc.solution.substitution_map.count(get_var('z')) > 0);
        const auto &z_subst = proc.solution.substitution_map.at(get_var('z'));
        CHECK(z_subst.size() == 1);
        const auto &z_tmp_var = z_subst[0];
        REQUIRE(proc.solution.substitution_map.count(get_var('x')) > 0);
        REQUIRE(proc.solution.substitution_map.at(get_var('x')).size() == 1);
        CHECK(z_tmp_var == proc.solution.substitution_map.at(get_var('x'))[0]);
        REQUIRE(proc.solution.aut_ass.count(z_tmp_var) > 0);
        CHECK(mata::nfa::are_equivalent(*(proc.solution.aut_ass.at(z_subst[0])), *regex_to_nfa("a")));

        CHECK(proc.solution.substitution_map.count(get_var('u')) == 1);
        CHECK(proc.solution.substitution_map.count(get_var('y')) == 1);
        CHECK(proc.solution.aut_ass.count(get_var('u')) == 0);
        CHECK(proc.solution.aut_ass.count(get_var('y')) == 0);

        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("unsat-two-equations", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        equalities.add_predicate(create_equality("yx", "r"));
        init_ass[get_var('x')] = regex_to_nfa("(a|b)*");
        init_ass[get_var('y')] = regex_to_nfa("(a|b)*");
        init_ass[get_var('z')] = regex_to_nfa("b");
        init_ass[get_var('u')] = regex_to_nfa("b*");
        init_ass[get_var('r')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("sat-two-equations", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        equalities.add_predicate(create_equality("yx", "r"));
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("a*");
        init_ass[get_var('u')] = regex_to_nfa("(a|b)*");
        init_ass[get_var('r')] = regex_to_nfa("aaa");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_true);
    }

    SECTION("unsat-two-equations-length", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        equalities.add_predicate(create_equality("yx", "r"));
        init_ass[get_var('x')] = regex_to_nfa("(a|b)*");
        init_ass[get_var('y')] = regex_to_nfa("(a|b)*");
        init_ass[get_var('z')] = regex_to_nfa("b");
        init_ass[get_var('u')] = regex_to_nfa("b*");
        init_ass[get_var('r')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { BasicTerm(BasicTermType::Variable, "x"), BasicTerm(BasicTermType::Variable, "z") }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("sat-two-equations-length", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("yx", "r"));
        equalities.add_predicate(create_equality("xy", "zu"));
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("ab*");
        init_ass[get_var('z')] = regex_to_nfa("ab*");
        init_ass[get_var('u')] = regex_to_nfa("a*");
        init_ass[get_var('r')] = regex_to_nfa("ab*a");
        DecisionProcedureCUT proc(equalities, init_ass, {
            BasicTerm(BasicTermType::Variable, "x"),
            BasicTerm(BasicTermType::Variable, "z") }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();

        REQUIRE(proc.compute_next_solution());

        proc.solution.flatten_substition_map();
        CHECK(mata::nfa::are_equivalent(proc.solution.aut_ass.get_automaton_concat(proc.solution.substitution_map.at(get_var('x'))), *regex_to_nfa("a")));
        CHECK(mata::nfa::are_equivalent(proc.solution.aut_ass.get_automaton_concat(proc.solution.substitution_map.at(get_var('z'))), *regex_to_nfa("a")));

        // FIXME: Length formula len is different than formula from lambda. Hashes are not equal.
        // auto l_vars = { BasicTerm(BasicTermType::Variable, "x"), BasicTerm(BasicTermType::Variable, "z") };
        // auto var_map = create_var_map(l_vars, m, m_util_s);
        // expr_ref len = proc.get_lengths(var_map);

        // // result as a lambda (different ordering of variables due to std::unordered_set)
        // auto resf = [&](std::vector<std::string> vc) {
        //     return expr_ref(m.mk_and(
        //     m.mk_and(
        //         m.mk_true(),
        //         m.mk_and(
        //             m.mk_or(
        //                 m.mk_false(),
        //                 m.mk_eq(m_util_s.str.mk_length(var_map.at(BasicTerm(BasicTermType::Variable, vc[0]))), m_util_a.mk_int(1))
        //             ),
        //             m_util_a.mk_ge(m_util_s.str.mk_length(var_map.at(BasicTerm(BasicTermType::Variable, vc[0]))), m_util_a.mk_int(0))
        //         )
        //     ),
        //     m.mk_and(
        //         m.mk_or(
        //             m.mk_false(),
        //             m.mk_eq(m_util_s.str.mk_length(var_map.at(BasicTerm(BasicTermType::Variable, vc[1]))), m_util_a.mk_int(1))
        //         ),
        //         m_util_a.mk_ge(m_util_s.str.mk_length(var_map.at(BasicTerm(BasicTermType::Variable, vc[1]))), m_util_a.mk_int(0))
        //     )
        //     ),
        // m);
        // };

        // CHECK(((resf({"x", "z"})->hash() == len->hash()) || (resf({"z", "x"})->hash() == len->hash())));
        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("sat-two-equations-length2", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("yx", "r"));
        equalities.add_predicate(create_equality("xy", "zu"));
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("ab*");
        init_ass[get_var('z')] = regex_to_nfa("ab*");
        init_ass[get_var('u')] = regex_to_nfa("a*");
        init_ass[get_var('r')] = regex_to_nfa("ab*a");
        DecisionProcedureCUT proc(equalities, init_ass, {
                BasicTerm(BasicTermType::Variable, "x"),
                BasicTerm(BasicTermType::Variable, "z"),
                BasicTerm(BasicTermType::Variable, "r") },
            m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();

        REQUIRE(proc.compute_next_solution());
        proc.solution.flatten_substition_map();
        CHECK(mata::nfa::are_equivalent(proc.solution.aut_ass.get_automaton_concat(proc.solution.substitution_map.at(get_var('x'))), *regex_to_nfa("a")));
        CHECK(mata::nfa::are_equivalent(proc.solution.aut_ass.get_automaton_concat(proc.solution.substitution_map.at(get_var('z'))), *regex_to_nfa("a")));
        CHECK(mata::nfa::are_equivalent(proc.solution.aut_ass.get_automaton_concat(proc.solution.substitution_map.at(get_var('r'))), *regex_to_nfa("aa")));

        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("unsat-simple-non-chain-free", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("x", "xx"));
        init_ass[get_var('x')] = regex_to_nfa("aa?b*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("sat-simple-non-chain-free", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("x", "xx"));
        init_ass[get_var('x')] = regex_to_nfa("a*b*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_true);
    }

    SECTION("unsat-simple-transducer", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_transducer(identity, "xy", "zu"));
        init_ass[get_var('x')] = regex_to_nfa("a");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("b");
        init_ass[get_var('u')] = regex_to_nfa("b*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("sat-simple-transducer", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_transducer(identity, "xy", "zu"));
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("a*");
        init_ass[get_var('u')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_true);
    }

    SECTION("unsat-two-equations-transducer", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_transducer(identity, "xy", "zu"));
        equalities.add_predicate(create_transducer(identity, "yx", "r"));
        init_ass[get_var('x')] = regex_to_nfa("(a|b)*");
        init_ass[get_var('y')] = regex_to_nfa("(a|b)*");
        init_ass[get_var('z')] = regex_to_nfa("b");
        init_ass[get_var('u')] = regex_to_nfa("b*");
        init_ass[get_var('r')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("sat-two-equations-transducer", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_transducer(identity, "xy", "zu"));
        equalities.add_predicate(create_transducer(identity, "yx", "r"));
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("a*");
        init_ass[get_var('u')] = regex_to_nfa("(a|b)*");
        init_ass[get_var('r')] = regex_to_nfa("aaa");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_true);
    }

    SECTION("sat-emptiness-transducer", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_transducer(transform_to_empty, "x", "y"));
        init_ass[get_var('x')] = regex_to_nfa("a");
        init_ass[get_var('y')] = regex_to_nfa("(a|b)*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        REQUIRE(proc.compute_next_solution() == lbool::l_true);
        CHECK(proc.get_model(get_var('x'), {}) == zstring("a"));
        CHECK(proc.get_model(get_var('y'), {}) == zstring(""));
    }

    SECTION("sat-emptiness-transducer2", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_transducer(transform_to_empty, "x", "y"));
        init_ass[get_var('x')] = regex_to_nfa("a+");
        init_ass[get_var('y')] = regex_to_nfa("(a|b)*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        REQUIRE(proc.compute_next_solution() == lbool::l_true);
        CHECK(proc.get_model(get_var('y'), {}) == zstring(""));
    }

    SECTION("unsat-emptiness-transducer", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_transducer(transform_to_empty, "y", "x"));
        init_ass[get_var('x')] = regex_to_nfa("a");
        init_ass[get_var('y')] = regex_to_nfa("(a|b)*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("sat-simple-transducer-length", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_transducer(identity, "x", "u"));
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('u')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { get_var('x'), get_var('u') }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        REQUIRE(proc.compute_next_solution() == lbool::l_true);
        auto [formula, precision] = proc.get_lengths();
        REQUIRE(precision == LenNodePrecision::PRECISE);
        CHECK(check_lia_sat(formula) == l_true);
        REQUIRE(formula.type == LenFormulaType::AND);
        formula.succ.push_back(LenNode{LenFormulaType::EQ, {get_var('x'), get_var('u')}});
        CHECK(check_lia_sat(formula) == l_true);
        formula.succ.back().type = LenFormulaType::NEQ;
        CHECK(check_lia_sat(formula) == l_false);
    }

    SECTION("sat-simple-transducer-length2", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_transducer(identity, "x", "u"));
        equalities.add_predicate(create_transducer(identity, "z", "x"));
        equalities.add_predicate(create_transducer(identity, "y", "z"));
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('u')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { get_var('y'), get_var('u') }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        REQUIRE(proc.compute_next_solution() == lbool::l_true);
        auto [formula, precision] = proc.get_lengths();
        REQUIRE(precision == LenNodePrecision::PRECISE);
        CHECK(check_lia_sat(formula) == l_true);
        REQUIRE(formula.type == LenFormulaType::AND);
        formula.succ.push_back(LenNode{LenFormulaType::EQ, {get_var('y'), get_var('u')}});
        CHECK(check_lia_sat(formula) == l_true);
        formula.succ.back().type = LenFormulaType::NEQ;
        CHECK(check_lia_sat(formula) == l_false);
    }

    SECTION("sat-simple-transducer-length3", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_transducer(identity, "x", "u"));
        equalities.add_predicate(create_transducer(identity, "z", "x"));
        equalities.add_predicate(create_transducer(identity, "y", "z"));
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('u')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { get_var('y'),  get_var('x'),  get_var('z'), get_var('u') }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        REQUIRE(proc.compute_next_solution() == lbool::l_true);
        auto [formula, precision] = proc.get_lengths();
        REQUIRE(precision == LenNodePrecision::PRECISE);
        CHECK(check_lia_sat(formula) == l_true);
        REQUIRE(formula.type == LenFormulaType::AND);
        formula.succ.push_back(LenNode{LenFormulaType::EQ, {get_var('y'), get_var('u')}});
        CHECK(check_lia_sat(formula) == l_true);
        formula.succ.back().type = LenFormulaType::NEQ;
        CHECK(check_lia_sat(formula) == l_false);
    }

    SECTION("sat-simple-transducer-length4", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_transducer(identity, "x", "u"));
        equalities.add_predicate(create_transducer(identity, "x", "z"));
        equalities.add_predicate(create_transducer(identity, "yy", "x"));
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('u')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { get_var('y'),  get_var('x'),  get_var('z'), get_var('u') }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        REQUIRE(proc.compute_next_solution() == lbool::l_true);
        auto [formula, precision] = proc.get_lengths();
        REQUIRE(precision == LenNodePrecision::PRECISE);
        CHECK(check_lia_sat(formula) == l_true);
        REQUIRE(formula.type == LenFormulaType::AND);
        formula.succ.push_back(LenNode{LenFormulaType::EQ, {LenNode{LenFormulaType::PLUS, {get_var('y'), get_var('y')}}, get_var('u')}});
        CHECK(check_lia_sat(formula) == l_true);
        formula.succ.back().type = LenFormulaType::NEQ;
        CHECK(check_lia_sat(formula) == l_false);
        formula.succ.back().succ[1] = get_var('z');
        CHECK(check_lia_sat(formula) == l_false);
        formula.succ.back().type = LenFormulaType::EQ;
        CHECK(check_lia_sat(formula) == l_true);
    }

    SECTION("queued on-cycle inclusions contribute length equalities") {
        DecisionProcedureCUT proc(
            Formula{}, init_ass, {}, m, m_util_s, m_util_a, {}, noodler_params);
        SolvingState state;
        const BasicTerm x{BasicTermType::Variable, "pending-length-x"};
        const BasicTerm a{BasicTermType::Literal, "a"};
        const Predicate forward = Predicate::create_equation({x, a}, {x});
        const Predicate reverse = forward.get_switched_sides_predicate();
        state.add_predicate(forward, true);
        state.add_predicate(reverse, true);
        state.enqueue_predicate(forward, false);
        state.enqueue_predicate(reverse, false);
        proc.solution = state;

        auto count_nodes = [](const LenNode& formula, LenFormulaType type) {
            size_t count = 0;
            std::function<void(const LenNode&)> visit = [&](const LenNode& node) {
                if (node.type == type) ++count;
                for (const LenNode& child : node.succ) visit(child);
            };
            visit(formula);
            return count;
        };

        LenNode pending_formula = proc.get_lengths().first;
        CHECK(count_nodes(pending_formula, LenFormulaType::EQ) == 1);
        CHECK(count_nodes(pending_formula, LenFormulaType::LEQ) == 1);

        proc.solution.remove_predicate_everywhere(forward);
        pending_formula = proc.get_lengths().first;
        CHECK(count_nodes(pending_formula, LenFormulaType::EQ) == 1);
        CHECK(count_nodes(pending_formula, LenFormulaType::LEQ) == 1);

        proc.solution.remove_predicate_everywhere(reverse);
        CHECK(proc.get_lengths().first.type == LenFormulaType::TRUE);
    }

    SECTION("queued off-cycle inclusions do not contribute length equalities") {
        DecisionProcedureCUT proc(
            Formula{}, init_ass, {}, m, m_util_s, m_util_a, {}, noodler_params);
        const BasicTerm x{BasicTermType::Variable, "off-cycle-length-x"};
        const BasicTerm a{BasicTermType::Literal, "a"};
        const Predicate inclusion = Predicate::create_equation({x, a}, {x});
        proc.solution.add_predicate(inclusion, false);
        proc.solution.enqueue_predicate(inclusion, false);

        CHECK(proc.get_lengths().first.type == LenFormulaType::TRUE);
    }
}

// Helper: make a Variable BasicTerm by name
static BasicTerm var(const std::string& name) {
    return BasicTerm(BasicTermType::Variable, name);
}

// Helper: make a Literal BasicTerm by value
static BasicTerm lit(const std::string& value) {
    return BasicTerm(BasicTermType::Literal, value);
}

TEST_CASE("grouped automata divisions isolate variables shared by inclusions", "[noodler]") {
    const BasicTerm A = var("division-A");
    const BasicTerm B = var("division-B");
    const BasicTerm C = var("division-C");
    const BasicTerm X = var("division-X");
    const BasicTerm Y = var("division-Y");

    auto make_state = [&]() {
        SolvingState state;
        state.aut_ass.set_alphabet({'a', 'b'});
        for (const BasicTerm& variable : {A, B, C}) {
            state.aut_ass[variable] = regex_to_nfa("(a|b)*");
        }
        return state;
    };

    auto add_both_orientations = [](SolvingState& state, const Predicate& inclusion) {
        state.add_predicate(inclusion, true, 1);
        state.add_predicate(inclusion.get_switched_sides_predicate(), true, 1);
    };

    SECTION("opposite orientations alone do not prevent grouping") {
        SolvingState state = make_state();
        const Predicate current = Predicate::create_equation({X}, {A, B, C});
        add_both_orientations(state, current);

        const auto& [automata, divisions] =
            state.get_automata_and_division_of_concatenation({A, B, C}, true);

        CHECK(automata.size() == 1);
        CHECK(divisions == std::vector<std::vector<BasicTerm>>{{A, B, C}});
    }

    SECTION("a variable occurring on both sides receives its own division") {
        SolvingState state = make_state();
        const Predicate current = Predicate::create_equation({A, X}, {A, B, C});
        add_both_orientations(state, current);

        const auto& [automata, divisions] =
            state.get_automata_and_division_of_concatenation({A, B, C}, true);

        CHECK(automata.size() == 2);
        CHECK(divisions == std::vector<std::vector<BasicTerm>>{{A}, {B, C}});
    }

    SECTION("a variable occurring in distinct inclusions receives its own division") {
        SolvingState state = make_state();
        const Predicate current = Predicate::create_equation({X}, {A, B, C});
        const Predicate other = Predicate::create_equation({Y}, {B});
        add_both_orientations(state, current);
        add_both_orientations(state, other);

        const auto& [automata, divisions] =
            state.get_automata_and_division_of_concatenation({A, B, C}, true);

        CHECK(automata.size() == 3);
        CHECK(divisions == std::vector<std::vector<BasicTerm>>{{A}, {B}, {C}});
    }
}

static bool process_local_for_test(
    SolvingState& state,
    const std::vector<Predicate>& left,
    const std::vector<Predicate>& right,
    std::set<BasicTerm>& substituted_vars,
    bool on_cycle)
{
    std::vector<LocalNoodleResult> results = process_substituting_inclusions(
        std::move(state), left, right, on_cycle, on_cycle ? 1 : 0, false);
    if (results.size() != 1) return false;
    state = std::move(results.front().state);
    substituted_vars = std::move(results.front().substituted_vars);
    return true;
}

TEST_CASE("Decision Procedure preprocesses literal first-last overlaps", "[noodler]") {
    smt_params params;
    ast_manager ast_m;
    reg_decl_plugins(ast_m);
    smt::context ctx{ast_m, params};
    theory_str_noodler_params noodler_params{};
    TheoryStrNoodlerCUT noodler{ctx, ast_m, noodler_params};

    const BasicTerm A = var("A");
    const BasicTerm B = var("B");

    SECTION("literal before the overlapping variable") {
        Formula equalities;
        equalities.add_predicate(Predicate::create_equation({lit("ab"), A}, {A, B}));

        AutAssignment init_ass;
        init_ass.set_alphabet({'a', 'b'});
        init_ass[A] = regex_to_nfa("(a|b)*");
        init_ass[B] = regex_to_nfa("ba");

        DecisionProcedureCUT proc(
            equalities, init_ass, {}, noodler.m, noodler.m_util_s, noodler.m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_true);
    }

    SECTION("literal after the overlapping variable") {
        Formula equalities;
        equalities.add_predicate(Predicate::create_equation({B, A}, {A, lit("ab")}));

        AutAssignment init_ass;
        init_ass.set_alphabet({'a', 'b'});
        init_ass[A] = regex_to_nfa("(a|b)*");
        init_ass[B] = regex_to_nfa("ba");

        DecisionProcedureCUT proc(
            equalities, init_ass, {}, noodler.m, noodler.m_util_s, noodler.m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_true);
    }

    SECTION("the overlap may be oriented from right to left") {
        Formula equalities;
        equalities.add_predicate(Predicate::create_equation({A, B}, {lit("ab"), A}));

        AutAssignment init_ass;
        init_ass.set_alphabet({'a', 'b'});
        init_ass[A] = regex_to_nfa("(a|b)*");
        init_ass[B] = regex_to_nfa("ba");

        DecisionProcedureCUT proc(
            equalities, init_ass, {}, noodler.m, noodler.m_util_s, noodler.m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_true);
    }

    SECTION("the original automaton assignment is retained") {
        Formula equalities;
        equalities.add_predicate(Predicate::create_equation({lit("ab"), A}, {A, lit("ba")}));

        AutAssignment init_ass;
        init_ass.set_alphabet({'a', 'b'});
        init_ass[A] = regex_to_nfa("b*");

        DecisionProcedureCUT proc(
            equalities, init_ass, {}, noodler.m, noodler.m_util_s, noodler.m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("an already periodic original language does not restart the overlap") {
        Formula equalities;
        equalities.add_predicate(Predicate::create_equation({lit("ab"), A}, {A, B}));

        AutAssignment init_ass;
        init_ass.set_alphabet({'a', 'b'});
        init_ass[A] = regex_to_nfa("(ab)*");
        init_ass[B] = regex_to_nfa("ba");

        DecisionProcedureCUT proc(
            equalities, init_ass, {}, noodler.m, noodler.m_util_s, noodler.m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_false);
    }
}

/**
 * Tests for SolvingState::process_substituting_inclusions_from_right and
 * process_substituting_inclusions_from_left in isolation.
 *
 * The original inclusion being processed in all three cases is:
 *     A · B · "a"  =  B · "b" · B          (A, B are length-sensitive)
 *
 * Shared constant layout used in every section:
 *   left_side_division  = { {A}, {B}, {"a"} }
 *   right_side_division = { {B}, {"b"}, {B} }
 */
TEST_CASE("process_substituting_inclusions", "[noodler]") {

    BasicTerm A  = var("A");
    BasicTerm B  = var("B");
    BasicTerm la = lit("a");
    BasicTerm lb = lit("b");

    // right_side_division and left_side_division are the same for all noodles
    // (they come from the original inclusion A·B·"a" = B·"b"·B)
    std::vector<std::vector<BasicTerm>> right_side_division = { {B}, {lb}, {B} };
    std::vector<std::vector<BasicTerm>> left_side_division  = { {A}, {B}, {la} };

    // Utility: build a SolvingState with fresh-var automata and the given length-sensitive vars.
    // The state has no inclusions/predicates yet (the original inclusion was removed before this point).
    auto make_state = [&](const std::vector<BasicTerm>& align_vars) -> SolvingState {
        SolvingState state;
        state.aut_ass.set_alphabet({'a', 'b'});
        // Assign a universal automaton to A and B so erase() can find them
        state.aut_ass[A] = regex_to_nfa("(a|b)*");
        state.aut_ass[B] = regex_to_nfa("(a|b)*");
        for (const BasicTerm& t : align_vars) {
            state.aut_ass[t] = regex_to_nfa("(a|b)*");
            state.length_sensitive_vars.insert(t);
        }
        state.length_sensitive_vars.insert(A);
        state.length_sensitive_vars.insert(B);
        return state;
    };

    // -------------------------------------------------------------------------
    // Noodle splits A·B·"a" = B·"b"·B into
    //   A    → [n8, "b"]
    //   B    → []
    //   "a"  → ["a"]
    //   --
    //   {B}  → [n8]
    //   {"b"}→ ["b"]
    //   {B}  → ["a"]
    //
    // Expected substitutions:
    //   B    → []
    //   n8   → []
    //   B    → ["a"]  (fails)
    //
    SECTION("substitution", "[noodler]") {
        BasicTerm n8 = var("@align_0!n8");

        SolvingState state = make_state({n8});

        std::vector<std::vector<BasicTerm>> left_side_vars_to_new_vars  = { {n8, lb}, {}, {la} };
        std::vector<std::vector<BasicTerm>> right_side_divisions_to_new_vars = { {n8}, {lb}, {la} };

        auto right_side_inclusions = util::create_inclusions_from_multiple_sides(
            right_side_divisions_to_new_vars, right_side_division);
        auto left_side_inclusions = util::create_inclusions_from_multiple_sides(
            left_side_division, left_side_vars_to_new_vars);

        std::set<smt::noodler::BasicTerm> substituted_vars;
        REQUIRE_FALSE(process_local_for_test(
            state, left_side_inclusions, right_side_inclusions, substituted_vars, true));
    }

    // -------------------------------------------------------------------------
    // Noodle splits A·B·"a" = B·"b"·B into
    //   A    → [n12]
    //   B    → [n13, "b"]
    //   "a"  → ["a"]
    //   --
    //   {B}  → [n12, n13]
    //   {"b"}→ ["b"]
    //   {B}  → ["a"]
    //
    // This candidate is infeasible: B → "a" turns the second left inclusion into
    // "a" = n13 · "b", so n13 → [] and then "a" = "b".
    // -------------------------------------------------------------------------
    SECTION("substitution2", "[noodler]") {
        BasicTerm n12 = var("@align_0!n12");
        BasicTerm n13 = var("@align_0!n13");

        SolvingState state = make_state({n12, n13});

        std::vector<std::vector<BasicTerm>> left_side_vars_to_new_vars  = { {n12}, {n13, lb}, {la} };
        std::vector<std::vector<BasicTerm>> right_side_divisions_to_new_vars = { {n12, n13}, {lb}, {la} };

        auto right_side_inclusions = util::create_inclusions_from_multiple_sides(
            right_side_divisions_to_new_vars, right_side_division);
        auto left_side_inclusions = util::create_inclusions_from_multiple_sides(
            left_side_division, left_side_vars_to_new_vars);

        std::set<smt::noodler::BasicTerm> substituted_vars;
        REQUIRE_FALSE(process_local_for_test(
            state, left_side_inclusions, right_side_inclusions, substituted_vars, true));
    }

    // -------------------------------------------------------------------------
    // Noodle splits A·B·"a" = B·"b"·B into
    //   A    → [n2]
    //   A    → ["b"]
    //   "a"  → ["a"]
    //   --
    //   {B}  → [n2]
    //   {"b"}→ ["b"]
    //   {B}  → ["a"]
    //
    // This candidate is infeasible: B → "b" turns the final right inclusion into
    // "a" = "b", so the other substitutions are unnecessary.
    // -------------------------------------------------------------------------
    SECTION("substitution3", "[noodler]") {
        BasicTerm n2 = var("@align_0!n2");

        SolvingState state = make_state({n2});

        std::vector<std::vector<BasicTerm>> left_side_vars_to_new_vars  = { {n2}, {lb}, {la} };
        std::vector<std::vector<BasicTerm>> right_side_divisions_to_new_vars = { {n2}, {lb}, {la} };

        auto right_side_inclusions = util::create_inclusions_from_multiple_sides(
            right_side_divisions_to_new_vars, right_side_division);
        auto left_side_inclusions = util::create_inclusions_from_multiple_sides(
            left_side_division, left_side_vars_to_new_vars);

        std::set<smt::noodler::BasicTerm> substituted_vars;
        REQUIRE_FALSE(process_local_for_test(
            state, left_side_inclusions, right_side_inclusions, substituted_vars, true));
    }
}

TEST_CASE("on-cycle noodle residuals preserve both orientations", "[noodler]") {
    const BasicTerm A = var("paired-A");
    const BasicTerm B = var("paired-B");
    const BasicTerm N = var("paired-N");
    const BasicTerm M = var("paired-M");

    auto make_state = [&](const std::vector<BasicTerm>& variables) {
        SolvingState state;
        state.aut_ass.set_alphabet({'a', 'b'});
        for (const BasicTerm& variable : variables) {
            state.aut_ass[variable] = regex_to_nfa("(a|b)*");
        }
        return state;
    };

    const Predicate left_residual = Predicate::create_equation({A, B}, {N});
    const Predicate right_residual = Predicate::create_equation({M}, {A, B});

    SECTION("unresolved on-cycle constraints add their switched forms") {
        SolvingState state = make_state({A, B, N, M});
        std::vector<LocalNoodleResult> results = process_substituting_inclusions(
            std::move(state), {left_residual}, {right_residual}, true, 1, false);

        REQUIRE(results.size() == 1);
        SolvingState& result = results.front().state;
        CHECK(result.inclusions == std::set<Predicate>{
            left_residual,
            left_residual.get_switched_sides_predicate(),
            right_residual,
            right_residual.get_switched_sides_predicate(),
        });
        CHECK(result.predicates_to_process.size() == 4);
    }

    SECTION("off-cycle constraints remain one-sided") {
        SolvingState state = make_state({A, B, N, M});
        std::vector<LocalNoodleResult> results = process_substituting_inclusions(
            std::move(state), {left_residual}, {right_residual}, false, 0, false);

        REQUIRE(results.size() == 1);
        const SolvingState& result = results.front().state;
        CHECK(result.inclusions == std::set<Predicate>{left_residual, right_residual});
        CHECK(result.predicates_to_process.size() == 1);
    }

    SECTION("an existing substitution produces a paired residual") {
        const BasicTerm P = var("paired-P");
        const BasicTerm Q = var("paired-Q");
        const BasicTerm N1 = var("paired-N1");
        const BasicTerm N2 = var("paired-N2");
        SolvingState state = make_state({P, Q, N1, N2});
        state.substitution_map[A] = {P, Q};

        std::vector<LocalNoodleResult> results = process_substituting_inclusions(
            std::move(state),
            {Predicate::create_equation({A}, {N1, N2})}, {}, true, 6, false);

        REQUIRE(results.size() == 1);
        const Predicate residual = Predicate::create_equation({P, Q}, {N1, N2});
        const SolvingState& result = results.front().state;
        CHECK(result.inclusions == std::set<Predicate>{
            residual, residual.get_switched_sides_predicate(),
        });
        CHECK(result.get_inclusion_depth(residual) == 7);
        CHECK(result.get_inclusion_depth(residual.get_switched_sides_predicate()) == 7);
        CHECK(result.predicates_to_process.size() == 2);
    }

    SECTION("a direct substitution needs no residual") {
        const BasicTerm N1 = var("substituted-N1");
        const BasicTerm N2 = var("substituted-N2");
        SolvingState state = make_state({A, N1, N2});

        std::vector<LocalNoodleResult> results = process_substituting_inclusions(
            std::move(state),
            {Predicate::create_equation({A}, {N1, N2})}, {}, true, 1, false);

        REQUIRE(results.size() == 1);
        const SolvingState& result = results.front().state;
        CHECK(result.inclusions.empty());
        REQUIRE(result.substitution_map.contains(A));
        CHECK(result.substitution_map.at(A) == std::vector<BasicTerm>{N1, N2});
    }
}

TEST_CASE("boundary-overlap acceleration in local noodles", "[noodler][overlap]") {
    const BasicTerm A = var("A");
    const BasicTerm X = var("X");
    const BasicTerm Y = var("Y");

    auto make_state = [&](const std::vector<std::pair<BasicTerm, std::string>>& assignments) {
        SolvingState state;
        state.aut_ass.set_alphabet({'a', 'b'});
        state.aut_ass[A] = regex_to_nfa("(a|b)*");
        state.aut_ass[X] = regex_to_nfa("(a|b)*");
        state.aut_ass[Y] = regex_to_nfa("a+");
        for (const auto& [term, language] : assignments) {
            state.aut_ass[term] = regex_to_nfa(language);
        }
        state.length_sensitive_vars.insert(A);
        return state;
    };

    SECTION("U V = V U recognizes either overlapping boundary from noodle coordinates") {
        const Predicate switched = Predicate::create_equation({X, A}, {A, X});

        SECTION("U is the prefix overlap") {
            const BasicTerm period_segment = var("uv-prefix-period");
            const BasicTerm shared = var("uv-prefix-shared");
            const BasicTerm tail_segment = var("uv-prefix-tail");
            SolvingState state = make_state({
                {A, "a+"}, {X, "a+"},
                {period_segment, "a+"}, {shared, "(a|b)+"},
                {tail_segment, "a+"},
            });
            state.add_predicate(switched, true);
            state.predicates_to_process.push(switched, false);

            std::vector<LocalNoodleResult> results = process_substituting_inclusions(
                std::move(state),
                {
                    Predicate::create_equation({A}, {period_segment, shared}),
                    Predicate::create_equation({X}, {tail_segment}),
                },
                {
                    Predicate::create_equation({period_segment}, {X}),
                    Predicate::create_equation({shared, tail_segment}, {A}),
                },
                true, 1, true);

            REQUIRE(results.size() == 1);
            const SolvingState& accelerated = results.front().state;
            REQUIRE(accelerated.substitution_map.contains(A));
            REQUIRE(accelerated.substitution_map.at(A).size() == 3);
            CHECK(accelerated.substitution_map.at(A).front() == X);
            CHECK_FALSE(accelerated.substitution_map.contains(X));
            CHECK_FALSE(accelerated.inclusions.contains(switched));
        }

        SECTION("V is the suffix overlap") {
            const BasicTerm head_segment = var("uv-suffix-head");
            const BasicTerm shared = var("uv-suffix-shared");
            const BasicTerm period_segment = var("uv-suffix-period");
            SolvingState state = make_state({
                {A, "a+"}, {X, "a+"},
                {head_segment, "a+"}, {shared, "(a|b)+"},
                {period_segment, "a+"},
            });
            state.add_predicate(switched, true);
            state.predicates_to_process.push(switched, false);

            std::vector<LocalNoodleResult> results = process_substituting_inclusions(
                std::move(state),
                {
                    Predicate::create_equation({A}, {head_segment}),
                    Predicate::create_equation({X}, {shared, period_segment}),
                },
                {
                    Predicate::create_equation({head_segment, shared}, {X}),
                    Predicate::create_equation({period_segment}, {A}),
                },
                true, 1, true);

            REQUIRE(results.size() == 1);
            const SolvingState& accelerated = results.front().state;
            REQUIRE(accelerated.substitution_map.contains(X));
            REQUIRE(accelerated.substitution_map.at(X).size() == 3);
            CHECK(accelerated.substitution_map.at(X).back() == A);
            CHECK_FALSE(accelerated.substitution_map.contains(A));
            CHECK_FALSE(accelerated.inclusions.contains(switched));
        }
    }

    SECTION("prefix transformation factors the bounded remainder through a fresh variable") {
        const BasicTerm y_segment = var("y-segment");
        const BasicTerm x_segment = var("x-segment");
        const BasicTerm shared = var("shared");
        SolvingState state = make_state({
            {y_segment, "a+"}, {x_segment, "(a|b)*"}, {shared, "(a|b)+"}
        });

        const Predicate switched = Predicate::create_equation({Y, A}, {A, X});
        state.add_predicate(switched, true);
        state.predicates_to_process.push(switched, false);
        const std::vector<Predicate> left{
            Predicate::create_equation({A}, {y_segment, shared}),
            Predicate::create_equation({X}, {x_segment}),
        };
        const std::vector<Predicate> right{
            Predicate::create_equation({y_segment}, {Y}),
            Predicate::create_equation({shared, x_segment}, {A}),
        };

        std::vector<LocalNoodleResult> results = process_substituting_inclusions(
            std::move(state), left, right, true, 1, true);
        REQUIRE(results.size() == 1);
        LocalNoodleResult result = std::move(results.front());
        SolvingState& accelerated = result.state;

        REQUIRE(accelerated.substitution_map.contains(A));
        REQUIRE(accelerated.substitution_map.at(A).size() == 3);
        CHECK(accelerated.substitution_map.at(A)[0] == Y);
        const BasicTerm a1 = accelerated.substitution_map.at(A)[1];
        const BasicTerm a2 = accelerated.substitution_map.at(A)[2];
        CHECK(a2 != shared);
        CHECK(accelerated.aut_ass.at(a2)->is_in_lang(mata::Word{}));
        CHECK(accelerated.aut_ass.at(a2)->is_in_lang(mata::Word{'a', 'b'}));
        CHECK(accelerated.aut_ass.contains(shared));
        CHECK(accelerated.length_sensitive_vars.contains(a1));
        CHECK(accelerated.length_sensitive_vars.contains(a2));
        CHECK(accelerated.length_sensitive_vars.contains(shared));
        CHECK(accelerated.length_sensitive_vars.contains(Y));
        CHECK_FALSE(accelerated.inclusions.contains(switched));
        CHECK_FALSE(accelerated.predicates_to_process.erase(switched));

        REQUIRE(accelerated.predicates_not_on_cycle.size() == 1);
        const Predicate carrier = *accelerated.predicates_not_on_cycle.begin();
        CHECK(carrier.get_left_side() == (std::vector<BasicTerm>{a1, a2}));
        CHECK(carrier.get_right_side() == (std::vector<BasicTerm>{shared}));
        CHECK(accelerated.predicates_to_process.top() == carrier);
        CHECK(accelerated.predicates_to_process.top_priority());

        std::optional<BasicTerm> factor_var;
        for (const Predicate& inclusion : accelerated.inclusions) {
            if (inclusion.get_left_side().size() == 2
                    && inclusion.get_left_side()[0] == a2
                    && inclusion.get_right_side() == std::vector<BasicTerm>{Y}) {
                factor_var = inclusion.get_left_side()[1];
                break;
            }
        }
        REQUIRE(factor_var.has_value());
        const BasicTerm v = *factor_var;
        CHECK(accelerated.aut_ass.at(v)->is_in_lang(mata::Word{}));
        CHECK(accelerated.aut_ass.at(v)->is_in_lang(mata::Word{'a', 'b'}));
        CHECK_FALSE(accelerated.length_sensitive_vars.contains(v));

        const Predicate period_factor = Predicate::create_equation({a2, v}, {Y});
        const Predicate x_factor = Predicate::create_equation({X}, {v, a2});
        const Predicate old_residual = Predicate::create_equation({a2, X}, {Y, a2});
        const Predicate commute = Predicate::create_equation({a1, Y}, {Y, a1});
        CHECK(accelerated.inclusions.contains(period_factor));
        CHECK(accelerated.inclusions.contains(period_factor.get_switched_sides_predicate()));
        CHECK(accelerated.inclusions.contains(x_factor));
        CHECK(accelerated.inclusions.contains(x_factor.get_switched_sides_predicate()));
        CHECK(accelerated.inclusions.contains(commute));
        CHECK(accelerated.inclusions.contains(commute.get_switched_sides_predicate()));
        CHECK_FALSE(accelerated.inclusions.contains(old_residual));
        CHECK_FALSE(accelerated.inclusions.contains(old_residual.get_switched_sides_predicate()));
        CHECK(accelerated.inclusions.size() == 7);
        CHECK(accelerated.get_inclusion_depth(period_factor) == 2);
        CHECK(accelerated.get_inclusion_depth(x_factor) == 2);

        PredicateQueue queue = accelerated.predicates_to_process;
        REQUIRE(queue.top() == carrier);
        queue.pop();
        while (!queue.empty()) {
            CHECK_FALSE(queue.top_priority());
            queue.pop();
        }
    }

    SECTION("suffix transformation") {
        const BasicTerm x_segment = var("suffix-x-segment");
        const BasicTerm y_segment = var("suffix-y-segment");
        const BasicTerm shared = var("suffix-shared");
        SolvingState state = make_state({
            {x_segment, "(a|b)*"}, {y_segment, "a+"}, {shared, "(a|b)*"}
        });
        const Predicate switched = Predicate::create_equation({A, Y}, {X, A});
        state.add_predicate(switched, true);
        state.predicates_to_process.push(switched, false);

        std::vector<LocalNoodleResult> results = process_substituting_inclusions(
            std::move(state),
            {
                Predicate::create_equation({X}, {x_segment}),
                Predicate::create_equation({A}, {shared, y_segment}),
            },
            {
                Predicate::create_equation({x_segment, shared}, {A}),
                Predicate::create_equation({y_segment}, {Y}),
            },
            true, 1, true);
        REQUIRE(results.size() == 1);
        const SolvingState& accelerated = results.front().state;
        REQUIRE(accelerated.substitution_map.at(A).size() == 3);
        const BasicTerm a2 = accelerated.substitution_map.at(A)[0];
        CHECK(a2 != shared);
        const BasicTerm a1 = accelerated.substitution_map.at(A)[1];
        CHECK(accelerated.substitution_map.at(A)[2] == Y);
        CHECK(accelerated.aut_ass.contains(shared));
        CHECK(accelerated.inclusions.contains(
            Predicate::create_equation({a2, a1}, {shared})));
        CHECK(accelerated.inclusions.contains(
            Predicate::create_equation({a1, Y}, {Y, a1})));

        std::optional<BasicTerm> factor_var;
        for (const Predicate& inclusion : accelerated.inclusions) {
            if (inclusion.get_left_side() == std::vector<BasicTerm>{X}
                    && inclusion.get_right_side().size() == 2
                    && inclusion.get_right_side()[0] == a2) {
                factor_var = inclusion.get_right_side()[1];
                break;
            }
        }
        REQUIRE(factor_var.has_value());
        const BasicTerm v = *factor_var;
        CHECK(accelerated.aut_ass.at(v)->is_in_lang(mata::Word{}));
        CHECK(accelerated.aut_ass.at(v)->is_in_lang(mata::Word{'a', 'b'}));
        CHECK_FALSE(accelerated.length_sensitive_vars.contains(v));

        const Predicate x_factor = Predicate::create_equation({X}, {a2, v});
        const Predicate period_factor = Predicate::create_equation({v, a2}, {Y});
        const Predicate old_residual = Predicate::create_equation({X, a2}, {a2, Y});
        CHECK(accelerated.inclusions.contains(x_factor));
        CHECK(accelerated.inclusions.contains(x_factor.get_switched_sides_predicate()));
        CHECK(accelerated.inclusions.contains(period_factor));
        CHECK(accelerated.inclusions.contains(period_factor.get_switched_sides_predicate()));
        CHECK_FALSE(accelerated.inclusions.contains(old_residual));
        CHECK_FALSE(accelerated.inclusions.contains(old_residual.get_switched_sides_predicate()));
        CHECK(accelerated.inclusions.size() == 7);
    }

    SECTION("nullable period forks independent ordinary and accelerated children") {
        const BasicTerm y_segment = var("nullable-y-segment");
        const BasicTerm x_segment = var("nullable-x-segment");
        const BasicTerm shared = var("nullable-shared");
        const BasicTerm untouched = var("nullable-untouched");
        SolvingState state = make_state({
            {y_segment, "a*"}, {x_segment, "(a|b)*"}, {shared, "(a|b)*"},
            {untouched, "(a|b)*"}
        });
        state.aut_ass[Y] = regex_to_nfa("a*");
        const Predicate switched = Predicate::create_equation({Y, A}, {A, X});
        state.add_predicate(switched, true);
        state.predicates_to_process.push(switched, false);

        std::vector<LocalNoodleResult> results = process_substituting_inclusions(
            std::move(state),
            {
                Predicate::create_equation({A}, {y_segment, shared}),
                Predicate::create_equation({X}, {x_segment}),
            },
            {
                Predicate::create_equation({y_segment}, {Y}),
                Predicate::create_equation({shared, x_segment}, {A}),
            },
            true, 1, true);
        REQUIRE(results.size() == 2);
        const size_t accelerated_children = static_cast<size_t>(std::count_if(
            results.begin(), results.end(), [&](const LocalNoodleResult& result) {
                auto it = result.state.substitution_map.find(A);
                return it != result.state.substitution_map.end() && it->second.size() == 3;
            }));
        CHECK(accelerated_children == 1);
        REQUIRE(results[0].state.aut_ass.contains(untouched));
        REQUIRE(results[1].state.aut_ass.contains(untouched));
        CHECK(results[0].state.aut_ass.at(untouched).get()
            != results[1].state.aut_ass.at(untouched).get());
    }

    SECTION("general acceleration does not require a stored switched predicate") {
        const BasicTerm y_segment = var("unpaired-y-segment");
        const BasicTerm x_segment = var("unpaired-x-segment");
        const BasicTerm shared = var("unpaired-shared");
        SolvingState state = make_state({
            {y_segment, "a+"}, {x_segment, "(a|b)*"}, {shared, "(a|b)*"}
        });

        std::vector<LocalNoodleResult> results = process_substituting_inclusions(
            std::move(state),
            {
                Predicate::create_equation({A}, {y_segment, shared}),
                Predicate::create_equation({X}, {x_segment}),
            },
            {
                Predicate::create_equation({y_segment}, {Y}),
                Predicate::create_equation({shared, x_segment}, {A}),
            },
            true,
            1,
            true);
        REQUIRE(results.size() == 1);
        const SolvingState& accelerated = results.front().state;
        REQUIRE(accelerated.substitution_map.at(A).size() == 3);
        CHECK(accelerated.substitution_map.at(A)[0] == Y);
        const BasicTerm a1 = accelerated.substitution_map.at(A)[1];
        const BasicTerm a2 = accelerated.substitution_map.at(A)[2];
        std::optional<BasicTerm> factor_var;
        for (const Predicate& inclusion : accelerated.inclusions) {
            if (inclusion.get_left_side().size() == 2
                    && inclusion.get_left_side()[0] == a2
                    && inclusion.get_right_side() == std::vector<BasicTerm>{Y}) {
                factor_var = inclusion.get_left_side()[1];
                break;
            }
        }
        REQUIRE(factor_var.has_value());
        const BasicTerm v = *factor_var;
        const Predicate period_factor = Predicate::create_equation({a2, v}, {Y});
        const Predicate x_factor = Predicate::create_equation({X}, {v, a2});
        const Predicate commute = Predicate::create_equation({a1, Y}, {Y, a1});
        CHECK(accelerated.inclusions.contains(
            Predicate::create_equation({a1, a2}, {shared})));
        CHECK(accelerated.inclusions.contains(period_factor));
        CHECK(accelerated.inclusions.contains(period_factor.get_switched_sides_predicate()));
        CHECK(accelerated.inclusions.contains(x_factor));
        CHECK(accelerated.inclusions.contains(x_factor.get_switched_sides_predicate()));
        CHECK(accelerated.inclusions.contains(commute));
        CHECK(accelerated.get_inclusion_depth(period_factor) == 2);
        CHECK(accelerated.get_inclusion_depth(x_factor) == 2);
        CHECK(accelerated.get_inclusion_depth(commute) == 2);
        CHECK(accelerated.inclusions.contains(commute.get_switched_sides_predicate()));
        CHECK_FALSE(accelerated.length_sensitive_vars.contains(v));
    }

    SECTION("literal acceleration does not require a stored switched predicate") {
        const BasicTerm x_segment = var("one-sided-x-segment");
        const BasicTerm period_segment = var("one-sided-period-segment");
        const BasicTerm shared = var("one-sided-shared");
        SolvingState state = make_state({
            {x_segment, "(a|b)*"}, {period_segment, "a"}, {shared, "(a|b)+"}
        });
        const BasicTerm word = lit("a");

        std::vector<LocalNoodleResult> results = process_substituting_inclusions(
            std::move(state),
            {
                Predicate::create_equation({X}, {x_segment}),
                Predicate::create_equation({A}, {shared, period_segment}),
            },
            {
                Predicate::create_equation({x_segment, shared}, {A}),
                Predicate::create_equation({period_segment}, {word}),
            },
            true,
            1,
            true);
        REQUIRE(results.size() == 1);
        const LocalNoodleResult& result = results.front();
        REQUIRE(result.state.substitution_map.at(A).size() == 3);
        const BasicTerm a2 = result.state.substitution_map.at(A)[0];
        CHECK(result.state.substitution_map.at(A)[2] == word);
        const Predicate residual = Predicate::create_equation({X, a2}, {a2, word});
        CHECK(result.state.inclusions.contains(residual));
        CHECK(result.state.inclusions.contains(residual.get_switched_sides_predicate()));
        CHECK(result.state.get_inclusion_depth(residual) == 2);
        CHECK(result.state.inclusions.size() == 3);
        CHECK(result.state.inclusions.contains(Predicate::create_equation(
            {a2, result.state.substitution_map.at(A)[1]}, {shared})));
    }

    SECTION("literal period uses word star and a proper prefix without a length bound") {
        const BasicTerm y_segment = var("literal-y-segment");
        const BasicTerm x_segment = var("literal-x-segment");
        const BasicTerm shared = var("literal-shared");
        SolvingState state = make_state({
            {y_segment, "ab"}, {x_segment, "(a|b)*"}, {shared, "(a|b)*"}
        });
        const BasicTerm word = lit("ab");
        const Predicate switched = Predicate::create_equation({word, A}, {A, X});
        state.add_predicate(switched, true);
        state.predicates_to_process.push(switched, false);

        std::vector<LocalNoodleResult> results = process_substituting_inclusions(
            std::move(state),
            {
                Predicate::create_equation({A}, {y_segment, shared}),
                Predicate::create_equation({X}, {x_segment}),
            },
            {
                Predicate::create_equation({y_segment}, {word}),
                Predicate::create_equation({shared, x_segment}, {A}),
            },
            true, 1, true);
        REQUIRE(results.size() == 1);
        const LocalNoodleResult& result = results.front();
        const SolvingState& accelerated = result.state;
        REQUIRE(accelerated.substitution_map.at(A).size() == 3);
        CHECK(accelerated.substitution_map.at(A)[0] == word);
        const BasicTerm a1 = accelerated.substitution_map.at(A)[1];
        const BasicTerm a2 = accelerated.substitution_map.at(A)[2];
        CHECK(a2 != shared);
        CHECK(accelerated.inclusions.size() == 3);
        CHECK(accelerated.inclusions.contains(
            Predicate::create_equation({a1, a2}, {shared})));
        CHECK(accelerated.aut_ass.at(a1)->is_in_lang(mata::Word{}));
        CHECK(accelerated.aut_ass.at(a1)->is_in_lang(mata::Word{'a', 'b'}));
        CHECK(accelerated.aut_ass.at(a1)->is_in_lang(mata::Word{'a', 'b', 'a', 'b'}));
        CHECK_FALSE(accelerated.aut_ass.at(a1)->is_in_lang(mata::Word{'a'}));
        CHECK(accelerated.aut_ass.at(a2)->is_in_lang(mata::Word{}));
        CHECK(accelerated.aut_ass.at(a2)->is_in_lang(mata::Word{'a'}));
        CHECK_FALSE(accelerated.aut_ass.at(a2)->is_in_lang(mata::Word{'a', 'b'}));
        CHECK(accelerated.inclusions.contains(
            Predicate::create_equation({a2, X}, {word, a2})));
    }

    SECTION("the remaining literal orientations use the specified factor order") {
        const BasicTerm word = lit("ab");
        auto run_literal = [&](bool suffix, bool use_period) {
            const BasicTerm x_segment = var(
                std::string("table-x-") + (suffix ? "s" : "p") + (use_period ? "y" : "x"));
            const BasicTerm y_segment = var(
                std::string("table-y-") + (suffix ? "s" : "p") + (use_period ? "y" : "x"));
            const BasicTerm shared = var(
                std::string("table-shared-") + (suffix ? "s" : "p") + (use_period ? "y" : "x"));
            SolvingState state = make_state({
                {x_segment, use_period ? "(a|b)*" : "ab"},
                {y_segment, use_period ? "ab" : "a+"},
                {shared, "(a|b)*"},
            });

            const std::vector<BasicTerm> original_x = use_period ? std::vector<BasicTerm>{X}
                                                                 : std::vector<BasicTerm>{word};
            const std::vector<BasicTerm> original_y = use_period ? std::vector<BasicTerm>{word}
                                                                 : std::vector<BasicTerm>{Y};
            const Predicate switched = suffix
                ? Predicate::create_equation({A, original_y[0]}, {original_x[0], A})
                : Predicate::create_equation({original_y[0], A}, {A, original_x[0]});
            state.add_predicate(switched, true);
            state.predicates_to_process.push(switched, false);

            std::vector<Predicate> left;
            std::vector<Predicate> right;
            if (!suffix) {
                left = {
                    Predicate::create_equation({A}, {y_segment, shared}),
                    Predicate::create_equation(original_x, {x_segment}),
                };
                right = {
                    Predicate::create_equation({y_segment}, original_y),
                    Predicate::create_equation({shared, x_segment}, {A}),
                };
            } else {
                left = {
                    Predicate::create_equation(original_x, {x_segment}),
                    Predicate::create_equation({A}, {shared, y_segment}),
                };
                right = {
                    Predicate::create_equation({x_segment, shared}, {A}),
                    Predicate::create_equation({y_segment}, original_y),
                };
            }

            std::vector<LocalNoodleResult> results = process_substituting_inclusions(
                std::move(state), left, right, true, 1, true);
            REQUIRE(results.size() == 1);
            return std::move(results.front());
        };

        LocalNoodleResult prefix_x = run_literal(false, false);
        REQUIRE(prefix_x.state.substitution_map.at(A).size() == 3);
        const BasicTerm prefix_x_a2 = prefix_x.state.substitution_map.at(A)[0];
        CHECK(prefix_x.state.substitution_map.at(A)[2] == word);
        CHECK(prefix_x.state.inclusions.contains(
            Predicate::create_equation({prefix_x_a2, word}, {Y, prefix_x_a2})));

        LocalNoodleResult suffix_x = run_literal(true, false);
        REQUIRE(suffix_x.state.substitution_map.at(A).size() == 3);
        CHECK(suffix_x.state.substitution_map.at(A)[0] == word);
        const BasicTerm suffix_x_a2 = suffix_x.state.substitution_map.at(A)[2];
        CHECK(suffix_x.state.inclusions.contains(
            Predicate::create_equation({word, suffix_x_a2}, {suffix_x_a2, Y})));

        LocalNoodleResult suffix_y = run_literal(true, true);
        REQUIRE(suffix_y.state.substitution_map.at(A).size() == 3);
        const BasicTerm suffix_y_a2 = suffix_y.state.substitution_map.at(A)[0];
        CHECK(suffix_y.state.substitution_map.at(A)[2] == word);
        CHECK(suffix_y.state.inclusions.contains(
            Predicate::create_equation({X, suffix_y_a2}, {suffix_y_a2, word})));

    }

    SECTION("both-literal selection uses the period word and rejects unequal lengths") {
        auto run_both_literal = [&](const zstring& x_word, const zstring& period_word) {
            const BasicTerm x_literal = BasicTerm(BasicTermType::Literal, x_word);
            const BasicTerm period_literal = BasicTerm(BasicTermType::Literal, period_word);
            const BasicTerm shared = var(
                "both-literal-shared-" + x_word.encode() + "-" + period_word.encode());
            SolvingState state = make_state({{shared, "(a|b)*"}});
            const Predicate switched =
                Predicate::create_equation({period_literal, A}, {A, x_literal});
            state.add_predicate(switched, true);
            state.predicates_to_process.push(switched, false);
            return process_substituting_inclusions(
                std::move(state),
                {
                    Predicate::create_equation({A}, {period_literal, shared}),
                    Predicate::create_equation({x_literal}, {x_literal}),
                },
                {
                    Predicate::create_equation({period_literal}, {period_literal}),
                    Predicate::create_equation({shared, x_literal}, {A}),
                },
                true,
                1,
                true);
        };

        std::vector<LocalNoodleResult> conjugate = run_both_literal("ba", "ab");
        REQUIRE(conjugate.size() == 1);
        const SolvingState& conjugate_state = conjugate.front().state;
        REQUIRE(conjugate_state.substitution_map.at(A).size() == 3);
        CHECK(conjugate_state.substitution_map.at(A)[0] == lit("ab"));
        const BasicTerm star = conjugate_state.substitution_map.at(A)[1];
        CHECK(conjugate_state.aut_ass.at(star)->is_in_lang(mata::Word{'a', 'b'}));
        CHECK_FALSE(conjugate_state.aut_ass.at(star)->is_in_lang(mata::Word{'b', 'a'}));

        CHECK(run_both_literal("a", "ab").empty());
        CHECK(run_both_literal("", "ab").empty());

        std::vector<LocalNoodleResult> both_empty = run_both_literal("", "");
        REQUIRE(both_empty.size() == 1);
    }
}

TEST_CASE("Equation Simplification", "[noodler]") {
    BasicTerm A = var("A");
    BasicTerm B = var("B");
    BasicTerm C = var("C");
    BasicTerm D = var("D");

    auto make_state = [&]() -> SolvingState {
        SolvingState state;
        state.aut_ass.set_alphabet({'a', 'b', 'c'});
        state.aut_ass[A] = regex_to_nfa("(a|b|c)*");
        state.aut_ass[B] = regex_to_nfa("(a|b|c)*");
        state.aut_ass[C] = regex_to_nfa("(a|b|c)*");
        return state;
    };

    SECTION("a one-sided literal surplus is rejected directly") {
        SolvingState state = make_state();
        Predicate inclusion = Predicate::create_equation(
            {A, B, C, lit("abc"), C},
            {B, lit("b"), A, lit("c")});

        std::vector<BasicTerm> simplified_left = inclusion.get_left_side();
        std::vector<BasicTerm> simplified_right = inclusion.get_right_side();
        Predicate::EquationSimplificationResult result =
            Predicate::simplify_equation(simplified_left, simplified_right);
        REQUIRE(result.kind == Predicate::EquationSimplificationResult::Kind::Infeasible);
        CHECK(result.residual.empty());

        std::set<BasicTerm> substituted_vars;
        REQUIRE_FALSE(process_local_for_test(state, {inclusion}, {}, substituted_vars, true));
    }

    SECTION("a per-symbol literal surplus needs an opposing variable surplus") {
        Predicate inclusion = Predicate::create_equation(
            {A, B, lit("bb"), C},
            {C, B, B, A, lit("a")});

        std::vector<BasicTerm> simplified_left = inclusion.get_left_side();
        std::vector<BasicTerm> simplified_right = inclusion.get_right_side();
        Predicate::EquationSimplificationResult result =
            Predicate::simplify_equation(simplified_left, simplified_right);

        REQUIRE(result.kind == Predicate::EquationSimplificationResult::Kind::Infeasible);
        CHECK(result.residual.empty());
    }

    SECTION("opposing variable surpluses can cover different literal surpluses") {
        Predicate inclusion = Predicate::create_equation(
            {A, lit("b")},
            {lit("a"), B});

        std::vector<BasicTerm> simplified_left = inclusion.get_left_side();
        std::vector<BasicTerm> simplified_right = inclusion.get_right_side();
        Predicate::EquationSimplificationResult result =
            Predicate::simplify_equation(simplified_left, simplified_right);

        CHECK(result.kind == Predicate::EquationSimplificationResult::Kind::NoConsequence);
    }

    SECTION("a variable-only consequence retains the ordering equation") {
        SolvingState state = make_state();
        Predicate inclusion = Predicate::create_equation({A, B}, {D, B, A, C});

        std::set<BasicTerm> substituted_vars;
        REQUIRE(process_local_for_test(state, {inclusion}, {}, substituted_vars, true));

        REQUIRE(substituted_vars == std::set<BasicTerm>{C, D});
        REQUIRE(state.substitution_map.at(C).empty());
        REQUIRE(state.substitution_map.at(D).empty());
        CHECK(state.inclusions.contains(Predicate::create_equation({A, B}, {B, A})));
    }

    SECTION("a self-embedding is reduced through its empty-side consequence") {
        BasicTerm X = var("X");
        SolvingState state = make_state();
        Predicate inclusion = Predicate::create_equation({X}, {A, X, B});

        std::set<BasicTerm> substituted_vars;
        REQUIRE(process_local_for_test(state, {inclusion}, {}, substituted_vars, true));

        CHECK(substituted_vars == std::set<BasicTerm>{A, B});
        CHECK(state.inclusions.empty());
    }

    SECTION("persistent inclusions also receive derived consequences") {
        BasicTerm D = var("D");
        SolvingState state = make_state();
        const Predicate source = Predicate::create_equation({A, B, D}, {B, A, C, D});
        state.add_predicate(source, true, 6);
        state.substitution_map[D] = {};

        REQUIRE(state.substitute_vars({D}));

        const Predicate simplified = Predicate::create_equation({A, B}, {B, A});
        const Predicate consequence = Predicate::create_equation({}, {C});
        CHECK(state.inclusions.contains(simplified));
        CHECK(state.inclusions.contains(consequence));
        CHECK(state.get_inclusion_depth(simplified) == 6);
        CHECK(state.get_inclusion_depth(consequence) == 6);
    }

    SECTION("substitution keeps the minimum depth when inclusions merge") {
        SolvingState state = make_state();
        const Predicate deeper = Predicate::create_equation({A, D}, {B});
        const Predicate shallower = Predicate::create_equation({A}, {B});
        state.add_predicate(deeper, true, 8);
        state.add_predicate(shallower, true, 2);
        state.substitution_map[D] = {};

        REQUIRE(state.substitute_vars({D}));

        REQUIRE(state.inclusions.size() == 1);
        CHECK(state.inclusions.contains(shallower));
        CHECK(state.get_inclusion_depth(shallower) == 2);
    }

    SECTION("split equations inherit off-cycle metadata") {
        SolvingState state = make_state();
        const Predicate source = Predicate::create_equation({A, B, D}, {B, A, C, D});
        state.add_predicate(source, false);
        state.substitution_map[D] = {};

        REQUIRE(state.substitute_vars({D}));

        const Predicate consequence = Predicate::create_equation({}, {C});
        REQUIRE(state.inclusions.contains(consequence));
        CHECK_FALSE(state.is_predicate_on_cycle(consequence));
        CHECK_FALSE(state.inclusion_depths.contains(consequence));
    }

    SECTION("removing an inclusion clears its depth") {
        SolvingState state = make_state();
        const Predicate inclusion = Predicate::create_equation({A}, {B});
        state.add_predicate(inclusion, true, 3);
        REQUIRE(state.inclusion_depths.contains(inclusion));

        state.remove_predicate(inclusion);

        CHECK_FALSE(state.inclusion_depths.contains(inclusion));
    }

    SECTION("balanced variables with different literal symbols are rejected") {
        SolvingState state = make_state();
        Predicate inclusion = Predicate::create_equation({A, lit("a")}, {lit("b"), A});

        std::set<BasicTerm> substituted_vars;
        REQUIRE_FALSE(process_local_for_test(state, {inclusion}, {}, substituted_vars, true));
    }

    SECTION("balanced literal symbols are not rejected for their order") {
        BasicTerm X = var("X");
        SolvingState state = make_state();
        Predicate inclusion = Predicate::create_equation({X, lit("ab")}, {lit("ba"), X});

        std::set<BasicTerm> substituted_vars;
        REQUIRE(process_local_for_test(state, {inclusion}, {}, substituted_vars, true));
        CHECK(substituted_vars.empty());
        CHECK(state.inclusions.contains(inclusion));
    }

    SECTION("persistent literal-symbol mismatch discards the state") {
        BasicTerm D = var("D");
        SolvingState state = make_state();
        state.add_predicate(
            Predicate::create_equation({A, lit("a"), D}, {lit("b"), A, D}), true);
        state.substitution_map[D] = {};

        REQUIRE_FALSE(state.substitute_vars({D}));
    }
}
