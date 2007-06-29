
let n =
	try int_of_string (Sys.argv.(1))
	with _ -> failwith "Usage: nqueens <n>"
;;

open Nqueens ;;

nqueens_co (fun board ->
	print_endline (string_of_plval board)
) (Int n) ;;
