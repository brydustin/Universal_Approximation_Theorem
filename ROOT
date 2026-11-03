(* All sessions must be in chapter AFP *)
chapter AFP

(* There must be one session with the (short) name of the entry.
   This session generates the web document and HTML files.

   It is strongly encouraged to have precisely one session, but 
   if needed, further sessions are permitted.

   Every theory must be included in at least one of the sessions.
*)

(* Base session HOL-Complex_Analysis: since Isabelle2026, HOL-Analysis provides the
   higher-differentiability development (C_k_on, Ck_on, real_analytic_on) and
   HOL-Complex_Analysis the complexification criterion used for analyticity.
   Smooth_Manifolds supplies the bump function that seeds the mollifier. The AFP entry
   "Lp" is not used: its scaleR instantiation for function types clashes with
   Smooth_Manifolds', so Lp_Inequalities.thy works from the Bochner integral. *)
session "Sigmoid_Universal_Approximation" = "HOL-Complex_Analysis" +

(* Timeout (in sec) in case of non-termination problems *)
  options [timeout = 600, document = pdf, document_output = "output", quick_and_dirty = false]

(* real_asymp, used for the sigmoid derivative limits. *)
  sessions
    "HOL-Real_Asymp"
    "HOL-Combinatorics"
    Smooth_Manifolds


(* To suppress document generation of some theories: *)
(*
  theories [document = false]
    This_Theory
    That_Theory
*)

(* The top-level theories of the submission: *)
  theories
    Sigmoid_Universal_Approximation

(* Dependencies on document source files: *)
  document_files
    "root.bib"
    "root.tex"
