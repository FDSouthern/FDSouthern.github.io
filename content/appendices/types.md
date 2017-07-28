lib.ml:521:type ('a,'b)func =


nets.ml:21:type term_label = Vnet                          (* variable (instantiable)   *)
nets.ml:26:type 'a net = Netnode of (term_label * 'a net) list * 'a list;;

preterm.ml:107:type pretype = Utv of string                   (* User type variable         *)
preterm.ml:130:type preterm = Varp of string * pretype       (* Variable           - v      *)

parser.ml:88:type lexcode = Ident of string

equal.ml:16:type conv = term->thm;;

drule.ml:16:type instantiation =

tactics.ml:25:type goal = (string * thm) list * term;;
tactics.ml:38:type justification = instantiation -> thm list -> thm;;
tactics.ml:45:type goalstate = (term list * instantiation) * goal list * justification;;
tactics.ml:51:type goalstack = goalstate list;;
tactics.ml:59:type refinement = goalstate -> goalstate;;
tactics.ml:71:type tactic = goal -> goalstate;;
tactics.ml:73:type thm_tactic = thm -> tactic;;
tactics.ml:75:type thm_tactical = thm_tactic -> thm_tactic;;


simp.ml:16:type gconv = int * conv;;
simp.ml:194:type prover = Prover of conv * (thm list -> prover);;
simp.ml:217:type simpset =

impconv.ml:738:type imp_conv = Variance.t -> term -> thm
impconv.ml:805:type 'a with_context =
impconv.ml:1072:type atomic = Atomic | Non_atomic
impconv.ml:1171:type annot_conv = term -> thm * term option * term list
impconv.ml:1438:type imp_mconv = Variance.t -> term -> thm list
impconv.ml:1607:type annot_mconv = term -> (thm * term option * term list) list

grobner.ml:19:type history =

realarith.ml:153:type positivstellensatz =
