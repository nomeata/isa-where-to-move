(*  Title: where_to_move.ML
    Author: Joachim Breitner

Utility commands to suggest lemma reorganisations.
*)

signature WHERE_TO_MOVE =
sig
  val thms_used_by_thm : thm -> string list
  val theories_used_by_thm : theory -> thm -> theory list
  val theories_used_by_thms : theory -> thm list -> theory list

  val theorems_used_by_cmd : (Facts.ref * Args.src list) list -> Toplevel.transition -> Toplevel.transition
  val where_to_move_cmd : (Facts.ref * Args.src list) list option -> Toplevel.transition -> Toplevel.transition
end

structure Where_To_Move : WHERE_TO_MOVE =
struct

fun thms_used_by_thm thm =
  let
  fun  used_by_proof_body (PBody {thms, ...}) = thms |> map #2 |> map go |> List.concat
  and go ("", _, pbodyf) = pbodyf |> Future.join |> used_by_proof_body
    | go (s, _, _) = [s]
  in thm |> Thm.proof_body_of |> Proofterm.strip_thm |> used_by_proof_body
  end;

fun nub ss = fold (fn x => Symtab.update (x, ())) ss Symtab.empty |> Symtab.keys;

fun theories_used_by_thm thy thm =
      thm |> thms_used_by_thm 
          |> map (hd o Long_Name.explode) 
          |> nub 
          |> map (Context.this_theory thy);

fun theories_used_by_thms thy thms =
      thms |> map thms_used_by_thm  |> List.concat
           |> map (hd o Long_Name.explode) 
           |> nub 
           |> map (Context.this_theory thy);


fun ok_for thys thy =
  forall (fn thy' => 
    let (* val _ = writeln (@{make_string} (theory_name thy', theory_name  thy,  Context.subthy (thy', thy))) *)
    in  Context.subthy (thy', thy) end) thys

fun better_theory thys this_thy =
  Context.ancestors_of this_thy 
  |> rev (* this way we get a minimal solution *)
  |> find_first  (ok_for thys);


fun theorems_used_by_cmd args = Toplevel.keep (fn state => 
    args |> Attrib.eval_thms (Toplevel.context_of state)
         |> map thms_used_by_thm
         |> map (Pretty.commas o map Pretty.str)
         |> map (Pretty.writeln o Pretty.paragraph)
         |> K ()
    );

(* singleton variant of eval_thms *)
fun eval_thm context arg = hd (Attrib.eval_thms context [arg])

(* from find_theormes.ML *)
fun pretty_ref _ thmref =
  let
    val (name, sel) =
      (case thmref of
        Facts.Named ((name, _), sel) => (name, sel)
      | Facts.Fact _ => raise Fail "Illegal literal fact");
  in Pretty.block
  (*     [Pretty.mark(#1 (Proof_Context.markup_extern_fact ctxt name)) (Pretty.str name), *)
    [Pretty.str name, Pretty.str (Facts.string_of_selection sel)]
  end;

fun facts_of_theory thy =
  let val prev_thys = (Theory.parents_of thy) 
      val facts = Global_Theory.facts_of thy
      val thms =  Facts.dest_static false (map Global_Theory.facts_of prev_thys) facts
  in thms end;

fun where_to_move_cmd args_o =
  Toplevel.keep ( fn state =>
    let val named_thms = case args_o of
            SOME args => args |> map (fn arg =>
              (Pretty.string_of (pretty_ref (Toplevel.context_of state) (#1 arg)),
              [ eval_thm (Toplevel.context_of state) arg] ))
            | NONE => facts_of_theory (Toplevel.theory_of state)
    in named_thms |> map (fn (name, thms) =>
    let  val thy = Toplevel.theory_of state
    in case better_theory (theories_used_by_thms thy thms) thy of
        SOME thy => Pretty.writeln (Pretty.paragraph
         [ Pretty.str "Theorem ", Pretty.str name,
           Pretty.str " could be moved to theory ",
           Pretty.quote (Pretty.str (Context.theory_name thy)), Pretty.str "."
         ])
      | NONE     => Pretty.writeln (Pretty.paragraph [Pretty.str "Theorem ", Pretty.str name, Pretty.str" is fine where it is."])
    end
    ) |> K ()
   end
   );


val _ = Outer_Syntax.improper_command @{command_spec "theorems_used_by"} 
    "prints all theorems used by the given theorem"
    (Parse_Spec.xthms1 >> theorems_used_by_cmd);

val _ = Outer_Syntax.improper_command @{command_spec "where_to_move"}
    "suggests a new location for the given theorem or, of none is given, all theorems in the current theory"
    (Scan.option Parse_Spec.xthms1 >> where_to_move_cmd);

end
