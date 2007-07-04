#ifdef MERCURY
#define insert ins
:- module nqueens.

:- interface.

:- import_module int, list.
:- pred nqueens(int::in,list(int)::out) is nondet.

:- implementation.
#endif

%:nqueens(+N,?Board)
nqueens(N,Board) :-
  range(1,N,L),
  permutation(L,Board),
  safe(Board).

%:range(+Start,+Stop,?Result)
#ifdef MERCURY
:- pred range(int::in,int::in,list(int)::out) is det.
range(M,N,L) :-
  O = ordering(M,N),
  ( O = (<), M1 is M+1, range(M1,N,L)
  ; (O = (=) ; O = (>)), L = [N]).
#else
range(M,N,[M|L]) :- M < N, M1 is M+1, range(M1,N,L).
range(N,N,[N]).
#endif

%:permutation(+List,?Result)
#ifdef MERCURY
:- pred permutation(list(T)::in,list(T)::out) is multi.
#endif
permutation([],[]).
permutation([A|M],N) :- permutation(M,N1), insert(A,N1,N).

%:insert(+Element,+List,?Result)
%:insert(?Element,+List,+Result)
%:insert(+Element,?List,+Result)
#ifdef MERCURY
:- pred insert(T,list(T),list(T)).
:- mode insert(in,in,out) is multi.
:- mode insert(out,in,in) is nondet.
:- mode insert(in,out,in) is nondet.
#endif
insert(A,L,[A|L]).
insert(A,[B|L],[B|L1]) :- insert(A,L,L1).

%:safe(+Board)
#ifdef MERCURY
:- pred safe(list(int)::in) is semidet.
#endif
safe([_]).
safe([Q|Qs]) :- nodiag(Q,Qs,1), safe(Qs).

%:nodiag(+Queen,+Board,+Dist)
#ifdef MERCURY
:- pred nodiag(int::in,list(int)::in,int::in) is semidet.
#endif
nodiag(_,[],_).
nodiag(Q1,[Q2|Qs],D) :-
  noattack(Q1,Q2,D),
#ifdef MERCURY
  D1=D+1,
#else
  D1 is D+1,
#endif
  nodiag(Q1,Qs,D1).

%:noattack(+Queen1,+Queen2,+Dist)
#ifdef MERCURY
:- pred noattack(int::in,int::in,int::in) is semidet.
#endif
noattack(Q1,Q2,D) :-
#ifdef MERCURY
  Q2-Q1 \= D,
  Q1-Q2 \= D.
#else
  Q2-Q1 =\= D,
  Q1-Q2 =\= D.
#endif
