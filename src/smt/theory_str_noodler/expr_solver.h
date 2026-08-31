/*
The skeleton of this code was obtained by Yu-Fang Chen from https://github.com/guluchen/z3. 
Eternal glory to Yu-Fang.
*/

#ifndef _EXPR_INT_SOLVER_H_
#define _EXPR_INT_SOLVER_H_

#include "smt/smt_kernel.h"
#include "params/smt_params.h"
#include "smt/smt_context.h"
#include "smt/theory_str_noodler/lia_solver.h"

namespace smt::noodler {
    class int_expr_solver : public lia_solver {
        bool unsat_core=false;
        ast_manager& m;
        smt_params m_fparams;
        bool initialized;
        expr_ref_vector erv;

        static smt_params string_solver_disabled(smt_params fp) {
            fp.m_string_solver = symbol("none");
            return fp;
        }

    public:
        kernel m_kernel;
    public:
        int_expr_solver(ast_manager& m, smt_params fp):
            m(m), m_fparams(string_solver_disabled(fp)), initialized(false), erv(m), m_kernel(m, m_fparams) {}

        lbool check_sat(expr* e) override;
        void initialize(context& ctx, bool include_assignment = true) override;
        void get_unsat_core(expr_ref& dst) override;
        void assert_expr(expr * e);
    };
}

#endif
