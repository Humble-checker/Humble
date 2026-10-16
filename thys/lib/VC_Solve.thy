theory VC_Solve
imports "Refine_Monadic.Refine_Misc"
begin

text \<open>
  This theory provides a tool for extracting definitions from terms, and
  for generating code equations for recursion combinators.
\<close>

ML \<open>
signature VC_SOLVE = sig
  val add_vc_rec_thm: thm -> Context.generic -> Context.generic
  val del_vc_rec_thm: thm -> Context.generic -> Context.generic
  val get_vc_rec_thms: Proof.context -> thm list

  val add_vc_solve_thm: thm -> Context.generic -> Context.generic
  val del_vc_solve_thm: thm -> Context.generic -> Context.generic
  val get_vc_solve_thms: Proof.context -> thm list

  val vc_solve_tac: Proof.context -> bool -> int -> tactic
  val vc_solve_modifiers: Method.modifier parser list

  val setup: theory -> theory
end

structure VC_Solve :VC_SOLVE = struct

    structure rec_thms = Named_Thms ( 
      val name = @{binding vcs_rec}
      val description = "VC-Solver: Recursive intro rules"
    )

    structure solve_thms = Named_Thms ( 
      val name = @{binding vcs_solve}
      val description = "VC-Solver: Solve rules"
    )

    val add_vc_rec_thm = rec_thms.add_thm
    val del_vc_rec_thm = rec_thms.del_thm
    val get_vc_rec_thms = rec_thms.get

    val add_vc_solve_thm = solve_thms.add_thm
    val del_vc_solve_thm = solve_thms.del_thm
    val get_vc_solve_thms = solve_thms.get

    val rec_modifiers = [
      Args.$$$ "rec" -- Scan.option Args.add -- Args.colon 
        >> K (Method.modifier rec_thms.add \<^here>),
      Args.$$$ "rec" -- Scan.option Args.del -- Args.colon 
        >> K (Method.modifier rec_thms.del \<^here>)
    ];

    val solve_modifiers = [
      Args.$$$ "solve" -- Scan.option Args.add -- Args.colon 
        >> K (Method.modifier solve_thms.add \<^here>),
      Args.$$$ "solve" -- Scan.option Args.del -- Args.colon 
        >> K (Method.modifier solve_thms.del \<^here>)
    ];

    val vc_solve_modifiers = 
      clasimp_modifiers @ rec_modifiers @ solve_modifiers;

    fun vc_solve_tac ctxt no_pre = let
      val rthms = rec_thms.get ctxt
      val sthms = solve_thms.get ctxt
      val pre_tac = if no_pre then K all_tac else clarsimp_tac ctxt
      val tac = SELECT_GOAL (auto_tac ctxt)
    in
      TRY o pre_tac
      THEN_ALL_NEW_FWD (TRY o REPEAT_ALL_NEW_FWD (resolve_tac ctxt rthms))
      THEN_ALL_NEW_FWD (TRY o SOLVED' (resolve_tac ctxt sthms THEN_ALL_NEW_FWD tac))
    end

    val setup = I
      #> rec_thms.setup 
      #> solve_thms.setup


end;
\<close>

setup VC_Solve.setup

text \<open>
  Method \<open>vc_solve (no_pre) clasimp_modifiers
    rec (add/del): ... solve (add/del): ...\<close>
  Named theorems \<open>vcs_rec\<close> and \<open>vcs_solve\<close>.

  This method is specialized to
  solve verification conditions. It first clarsimps all goals, then
  it tries to apply a set of safe introduction rules (\<open>vcs_rec\<close>, \<open>rec add\<close>).
  Finally, it applies introduction rules (\<open>vcs_solve\<close>, \<open>solve add\<close>) and tries
  to discharge all emerging subgoals by auto. If this does not succeed, it
  backtracks over the application of the solve-rule.
\<close>

method_setup vc_solve = 
  \<open>Scan.lift (Args.mode "nopre") 
      --| Method.sections VC_Solve.vc_solve_modifiers >>
  (fn (nopre) => fn ctxt => SIMPLE_METHOD (
    CHANGED (ALLGOALS (VC_Solve.vc_solve_tac ctxt nopre))
  ))\<close> "Try to solve verification conditions"


end
