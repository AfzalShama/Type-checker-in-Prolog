%%%%%%%%%%%%%% Looking-up the var in Gamma %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

listing(lookup/3).

lookup([], var(X), T) :- fail.

lookup([pair(X, T1) | GS], var(X), T) :- T = T1, !. 

lookup([pair(Y, _) | GS], V, T) :- lookup(GS, V, T1), T = T1.



%%%%%%%%%%%%%%%% Type Checking %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

hastype(Gamma, constInt(C), intT).

hastype(Gamma, constBool(B), boolT). 

hastype(Gamma, var(X), T) :- lookup(Gamma, var(X), T).


hastype(Gamma, add(E1, E2), intT) :- hastype(Gamma, E1, intT), 
										 hastype(Gamma, E2, intT).

hastype(Gamma, subtract(E1, E2), intT) :- hastype(Gamma, E1, intT), 
										 hastype(Gamma, E2, intT).

hastype(Gamma, multiply(E1, E2), intT) :- hastype(Gamma, E1, intT), 
										 hastype(Gamma, E2, intT).

hastype(Gamma, divide(E1, E2), intT) :- hastype(Gamma, E1, intT), 
										 hastype(Gamma, E2, intT).


hastype(Gamma, and(E1, E2), boolT) :- hastype(Gamma, E1, boolT),
									 	 hastype(Gamma, E2, boolT).

hastype(Gamma, or(E1, E2), boolT) :- hastype(Gamma, E1, boolT),
									 	 hastype(Gamma, E2, boolT).

hastype(Gamma, implies(E1, E2), boolT) :- hastype(Gamma, E1, boolT),
									 	 hastype(Gamma, E2, boolT).

hastype(Gamma, not(E), boolT) :- hastype(Gamma, E, boolT).


hastype(Gamma, greater(E1, E2), boolT) :- hastype(Gamma, E1, intT),
									 	 hastype(Gamma, E2, intT).

hastype(Gamma, lesser(E1, E2), boolT) :- hastype(Gamma, E1, intT),
									 	 hastype(Gamma, E2, intT).


hastype(Gamma, equals(E1, E2), boolT) :- hastype(Gamma, E1, T1),
									  	  hastype(Gamma, E2, T2).

hastype(Gamma, ifte(e, E1, E2), T) :- hastype(Gamma, e, boolT),
									  hastype(Gamma, E1, T1),
									  hastype(Gamma, E2, T1).

hastype(Gamma, def(D, E), T) :- typeElaborates(Gamma, D, Gamma1),
								append(Gamma, Gamma1, Gamma_new),
								hastype(Gamma_new, E, T).

hastype(Gamma, lambda(X, E), arrow(T1, T2)) :- hastype([pair(X, T1) | Gamma], E, T2). 

hastype(Gamma, app(E1, E2), T2) :- hastype(Gamma, E1, arrow(T1, T2)), 
								   hastype(Gamma, E2, T1).

hastype(Gamma, nTuple([]), T).
hastype(Gamma, nTuple([X | XS]), T) :- hastype(Gamma, X, T),
									   hastype(Gamma, nTuple(XS), T).

hastype(Gamma, proj(I, NT), T) :- hastype(Gamma, I, intT),
								  hastype(Gamma, nTuple(NT), T).

hastype(Gamma, left(E), T) :- hastype(Gamma, E, T).
hastype(Gamma, right(E), T) :- hastype(Gamma, E, T).

hastype(Gamma, case(E1, E2), T) :- hastype(Gamma, E1, T),
								   hastype(Gamma, E2, T).

intersection(Gamma, []).
intersection(Gamma, [pair(X, T) | B]) :- lookup(Gamma, var(X), T), !, fail.
intersection(Gamma, [pair(Y, T) | B]) :- intersection(Gamma, B).


%%%%%%%%%%%% Extending the Gamma Table wrt Definitions %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

typeElaborates(Gamma, defVar(X, E), Gamma1) :- hastype(Gamma, E, T),
											   Gamma1 = [pair(X, T)].

typeElaborates(Gamma, defCons(D1, D2), Gamma3) :- typeElaborates(Gamma, D1, Gamma1),
												 append(Gamma, Gamma1, Gamma_new),
												 typeElaborates(Gamma_new, D2, Gamma2),
												 append(Gamma1, Gamma2, Gamma3).

typeElaborates(Gamma, defOr(D1, D2), Gamma3) :- typeElaborates(Gamma, D1, Gamma1),
											    append(Gamma, Gamma1, Gamma_new), 
											    typeElaborates(Gamma_new, D2, Gamma2),
											    intersection(Gamma1, Gamma2),
											    append(Gamma1, Gamma2, Gamma3).

typeElaborates(Gamma, defLocal(D1, D2), Gamma2) :- typeElaborates(Gamma, D1, Gamma1),
												   append(Gamma, Gamma1, Gamma_new),
												   typeElaborates(Gamma_new, D2, Gamma2).


