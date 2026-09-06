theory Proof_Audit
  imports Sigmoid_Universal_Approximation.Sigmoid_Universal_Approximation
begin

(* Build safeguard: audit stored proofs, not a numbered result in the paper. *)
ML \<open>
  val audit_thy = @{theory};
  val audit_base = Thy_Info.get_theory "Real_and_Complex_Analytic.Higher_Differentiability";
  val audit_facts = Global_Theory.dest_thms true [audit_base] audit_thy
    |> map (apsnd (Thm.transfer audit_thy));
  (* The directory scanned is the ENTRY's, not this theory's. Proof_Audit.thy lives in
     its own session directory, because Isabelle forbids two sessions sharing one; if
     this scanned its own directory it would find only itself and the check that every
     local theory file lies in the import closure would be vacuous. *)
  val audit_root = Thy_Info.get_theory
    "Sigmoid_Universal_Approximation.Sigmoid_Universal_Approximation";
  val audit_dir = Resources.master_directory audit_root;
  fun audit_directory thy = Path.implode (Path.expand (Resources.master_directory thy));
  val audit_names = audit_thy :: Context.ancestors_of audit_thy
    |> filter (fn thy => audit_directory thy = audit_directory audit_root)
    |> map Context.theory_base_name;
  val audit_files = File.read_dir audit_dir
    |> filter (String.isSuffix ".thy")
    |> map (fn name => String.substring (name, 0, size name - 4));
  val audit_missing = subtract (op =) audit_names audit_files;
  val _ = if null audit_missing then
      writeln ("AUDIT: all " ^ Int.toString (length audit_files) ^ " local theory files are loaded")
    else error ("AUDIT: local theory files outside the import closure: " ^ commas audit_missing);
  fun audit_is_project name = exists (fn theory_name =>
    String.isPrefix (theory_name ^ ".") name orelse
    String.isPrefix ("Sigmoid_Universal_Approximation." ^ theory_name ^ ".") name) audit_names;
  val audit_project_facts = filter (fn (((name, _), _), _) => audit_is_project name) audit_facts;
  val _ = if null audit_project_facts then error "AUDIT: no project facts selected" else ();
  val audit_oracles = Thm_Deps.all_oracles (map #2 audit_project_facts);
  val _ = if null audit_oracles then ()
    else error (Pretty.string_of
      (Thm_Deps.pretty_thm_oracles @{context} (map #2 audit_project_facts)));
  val _ = writeln ("AUDIT: " ^ Int.toString (length audit_project_facts) ^
    " project fact entries checked; no transitive oracle dependencies");
  val audit_hyps = filter (fn (_, th) => not (null (Thm.hyps_of th))) audit_project_facts;
  val _ = if null audit_hyps then writeln "AUDIT: no hidden theorem hypotheses"
    else error "AUDIT: hidden theorem hypotheses found";
  val audit_frees = filter (fn (_, th) => not (null (Term.add_frees (Thm.prop_of th) [])))
    audit_project_facts;
  val _ = List.app (fn (((name, _), _), th) => writeln ("AUDIT free variables: " ^ name ^
    " : " ^ commas (map #1 (Term.add_frees (Thm.prop_of th) [])))) audit_frees;
  val _ = if null audit_frees then writeln "AUDIT: 0 fact entries with fixed free term variables"
    else error "AUDIT: fixed free term variables found";
  val audit_new_axioms = filter (fn (name, _) => audit_is_project name)
    (Theory.all_axioms_of audit_thy);
  val _ = if forall (fn (name, _) => String.isSuffix "_def_raw" name) audit_new_axioms then ()
    else error "AUDIT: non-definitional project axiom found";
  val _ = writeln ("AUDIT: session axioms/definitions: " ^
    commas (map #1 audit_new_axioms));
\<close>

end
