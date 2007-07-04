:- module nqueens_mercury.
:- interface.

:- import_module io.
:- pred main(io::di, io::uo) is cc_multi.

:- implementation.

:- import_module int, list, string, nqueens, solutions.

:- pred print_sol(list(int)::in, io::di, io::uo) is det.
print_sol(Sol) -->
  write(Sol),
  nl.

main -->
  command_line_arguments(Args),
  (if
    { Args=[S], string.to_int(S,N) }
  then
    unsorted_aggregate(
      pred(Board::out) is nondet :- nqueens(N,Board),
	print_sol
    )
  else
    write_string("Usage: nqueens <n>\n")
  ).
