open Parser ;;
open Camlp4.PreCast ;;

Gram.Entry.clear Syntax.implem;

EXTEND Gram
GLOBAL: Syntax.implem;

Syntax.implem:
	[ [ p = prog; `EOI ->
		(List.concat
			[Translate.prog_statics _loc p; Translate.prog_rules _loc p]),
		None
	] ];
END ;;


