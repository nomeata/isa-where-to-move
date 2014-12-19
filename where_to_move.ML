(*  Title: where_to_move.ML
    Author: Joachim Breitner

Utility commands to suggest lemma reorganisations.
*)

signature WHERE_TO_MOVE =
sig
  val thms_used_by_thm : thm -> string list
  val theories_used_by_thm : theory -> thm -> theory list
  val theories_used_by_thms : theory -> thm list -> theory list

  val theorems_used_by_cmd : (string * Position.T) -> Toplevel.transition -> Toplevel.transition
  val where_to_move_cmd : (string * Position.T) list option -> Toplevel.transition -> Toplevel.transition
end

structure Where_To_Move : WHERE_TO_MOVE =
struct

fun thms_used_by_thm thm =
  let
  fun  used_by_proof_body (PBody {thms, ...}) = thms |> map #2 |> maps go
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
      thms |> maps thms_used_by_thm
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


fun theorems_used_by_cmd arg = Toplevel.keep (fn state =>
    let val ctxt = Toplevel.context_of state
        val thy = Toplevel.theory_of state
        val (_, thms) =  Facts.retrieve (Context.Proof ctxt) (Global_Theory.facts_of thy) arg
    in thms |> maps thms_used_by_thm
            |> map (Pretty.mark_str o Proof_Context.markup_extern_fact ctxt)
            |> Pretty.commas
            |> Pretty.paragraph
            |> Pretty.writeln
    end
    );


fun facts_of_theory thy =
  let val prev_thys = (Theory.parents_of thy) 
      val facts = Global_Theory.facts_of thy
      val thms =  Facts.dest_static false (map Global_Theory.facts_of prev_thys) facts
  in thms end;

fun where_to_move_cmd args_o =
  Toplevel.keep ( fn state =>
    let val ctxt = Toplevel.context_of state
        val this_thy = Toplevel.theory_of state
        val (verbose, named_thms) = case args_o of
            SOME args => (true, args |> map (Facts.retrieve (Context.Proof ctxt) (Global_Theory.facts_of this_thy)))
            | NONE =>    (false, facts_of_theory this_thy)
    in named_thms |> map (fn (name, thms) =>
      let val pretty_name = Proof_Context.markup_extern_fact ctxt name |> Pretty.mark_str |> Pretty.quote
      in case better_theory (theories_used_by_thms this_thy thms) this_thy of
          SOME thy =>
           [ Pretty.str "Theorem ", pretty_name,
             Pretty.str " could be moved to theory ",
             Pretty.quote (Pretty.mark_str (Theory.get_markup thy, Context.theory_name thy)),
             Pretty.str "."
           ] |> Pretty.paragraph |> Pretty.writeln
        | NONE =>
          if verbose then
           [ Pretty.str "Theorem ", pretty_name,
             Pretty.str" is fine where it is."] |> Pretty.paragraph |> Pretty.writeln
          else ()
      end
    ) |> K ()
   end
   );


val _ = Outer_Syntax.improper_command @{command_spec "theorems_used_by"} 
    "prints all theorems used by the given theorem"
    (Parse.position Parse.xname >> theorems_used_by_cmd);

val _ = Outer_Syntax.improper_command @{command_spec "where_to_move"}
    "suggests a new location for the given theorem or, of none is given, all theorems in the current theory"
    (Scan.option (Scan.repeat1 (Parse.position Parse.xname)) >> where_to_move_cmd);

end
