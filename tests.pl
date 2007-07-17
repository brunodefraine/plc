
(* Since not is so important, we test it first. *)

pred0(a).
pred0(b).
error0a :- not(pred0(a)).
error0a :- not(pred0(b)).
error0b :- pred0(c).
error0c :- not(not(pred0(c))).
error0d :- not(pred0(a)), pred0(a).
error0d :- pred0(a), not(pred0(a)).

(* sibling *)
parent(theo,maja).
parent(theo,ellie).
pred1(X,Y) :- parent(Z,X), parent(Z,Y), X\=Y.
ok1a(maja,ellie).
ok1a(ellie,maja).
error1a :- pred1(X,Y), not(ok1a(X,Y)).
error1b :- pred1(theo,maja).
error1b :- pred1(theo,ellie).
error1c :- pred1(maja,X), X\=ellie.

(* unification *)
%:pred2(?A,+B,?C)
%:pred2(+A,?B,+C)
pred2(a,X,X).
pred2(X,X,b).
ok2a(a,c).
ok2a(c,b).
error2a :- pred2(X,c,Y), not(ok2a(X,Y)).
error2b :- pred2(a,c,b).
error2c :- not(pred2(c,c,b)).
error2c :- not(pred2(a,c,c)).
error2c :- not(pred2(a,a,b)).
ok2d(a).
ok2d(b).
error2d :- pred2(X,b,b), not(ok2d(X)).

(* compounds *)
pred3(foo(a,b)).
error3a :- pred3(a).
error3a :- pred3(foo(a,c)).
error3a :- pred3(foo(c,b)).
error3a :- pred3(bar(a,b)).
error3b :- pred3(X), X\=foo(a,b).
ok3c(a,b).
error3c :- pred3(foo(X,Y)), not(ok3c(X,Y)).

(* compounds (lists) and unification *)
%:pred4(+List)
pred4([X,X|_]).
error4a :- pred4([a,b,c]).
error4a :- pred4([a,b,b]).
error4b :- not(pred4([a,a,b])).

(* integer arithmetic *)
error5a :- X is 1-2+3, X\=2 .
error5a :- not(2 is 1-2+3).
error5a :- X is 1-(2+3), X\=(-4).
error5b :- a is 1+1 .
error5c :- X1 is 1-2, X is X1+3, X\=2 .
error5d :- X=1, Y=2, 3+X+Y =\= Y+X+3 .
error5d :- X=1, Y=2, X-Y =:= Y-X.

(* cut *)
ab(a).
ab(b).
bc(b).
bc(c).
pred6(X,Y) :- ab(X), !, bc(Y).
pred6(c,a).
ok6a(a,b).
ok6a(a,c).
error6a :- pred6(X,Y), not(ok6a(X,Y)).
error6b :- not(pred6(c,a)).
error6b :- not(pred6(b,b)).
error6b :- not(pred6(a,c)).
error6c :- pred6(a,a).
