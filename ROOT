(* All sessions must be in chapter AFP *)
chapter AFP

(* There must be one session with the (short) name of the entry.
   This session generates the web document and HTML files.

   It is strongly encouraged to have precisely one session, but 
   if needed, further sessions are permitted.

   Every theory must be included in at least one of the sessions.
*)

(* Session name, list base session: Real_and_Complex_Analytic provides the canonical
   Ck_on / k_times_Fr_differentiable_at higher-differentiability development (real and
   multi-dimensional), used in place of this project's own former Nth_derivative / C_k_on.
   (The AFP entry "Lp" was tried for Section 3's L^p norm but its Functional_Spaces theory's
   scaleR instantiation for function types is irreconcilably incompatible with the scaleR
   instantiation Real_and_Complex_Analytic needs from Smooth_Manifolds -- a hard Isabelle
   class-specification clash, not a design choice -- so Lp_Approximation.thy instead defines
   Lp_norm directly via the Bochner integral, with no AFP Lp dependency.) *)
session "Sigmoid_Universal_Approximation" = "Real_and_Complex_Analytic" +

(* Timeout (in sec) in case of non-termination problems *)
  options [timeout = 600, document = pdf, document_output = "output", quick_and_dirty = false]


(* To suppress document generation of some theories: *)
(*
  theories [document = false]
    This_Theory
    That_Theory
*)

(* The top-level theories of the submission: *)
  theories
    Sigmoid_Universal_Approximation
    Proof_Audit

(* Dependencies on document source files: *)
  document_files
    "root.bib"
    "root.tex"
