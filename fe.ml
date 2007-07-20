open Parser ;;
open Camlp4.PreCast ;;

let group_rs = ref Translate.group_rs ;;

Camlp4.Options.add "-nogroup" (Arg.Unit (fun () ->
	group_rs := Translate.nogroup_rs))
	"Don't try to optimally group predicate rules" ;;

Gram.Entry.clear Syntax.implem;

EXTEND Gram
GLOBAL: Syntax.implem;

Syntax.implem:
	[ [ p = prog; `EOI ->
		(List.concat
			[Translate.prog_statics _loc p; Translate.prog_rules _loc !group_rs p]),
		None
	] ];
END ;;


