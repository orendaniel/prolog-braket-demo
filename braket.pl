/* NOTE - this is a demonstration, writing a "real" roboust system which
	Also implements tensoric product is quite hard so its avoided */

 /* Simplifier */

/**************************************************/

% This simplifier is intentionally made to be simple over complete 
% It also INTENTIONALLY avoids modern extensions like CFD and sticks to "classical prolog",
% Hence the extensive use of cut.
% This simplifier is directly adopted from "Clause and Effect".

% Simplify until no further simplifications are possible
simp(X, Y) :-
	s_step(X, Next),
	X \== Next, !,
	simp(Next, Y).

simp(X, X).


% Simplify Matrix Form
simpmat([], []).
simpmat([[H|T]|Z], [R|S])	:- !, simpmat([H|T], R), simpmat(Z, S).
simpmat([H|T], [R|S])		:- simp(H,R), simpmat(T, S).

% Simplification step, to preform reduction

s_step(Term, X) :-
	compound(Term), !,
	Term =.. [F | Args], 					% seperate functor from args
	maplist(s_step, Args, Mapped_args), 	% simplify args
	New_term =.. [F | Mapped_args],	  		% recombine
	reduc(New_term, X).				 		% reduce the functor

s_step(X, X).

% Reduction rules

% Notation reduction - refactor prolog's representation
reduc(A * -B, -(A * B)).
reduc(-A * B, -(A * B)).
reduc(A + -B, A - B).
reduc(A - -B, A + B).
reduc(-1 * A, -A).
reduc(A * -1, -A).
reduc(- -A, A).
reduc(-(A), B) 		:- number(A), B is -1*A.
reduc(-(A*B), C*B) 	:- number(A), C is -1*A.


% Associativity
reduc((A*B)*C, A*(B*C)). % associativity

% Imaginery
reduc(i*i, -1).
reduc(i*A, A*i) :- A \== i, !.

% Arithmatic reduction (handles floats too).
reduc(A+B, C)	 :- number(A), number(B), C is A+B.
reduc(A-B, C)	 :- number(A), number(B), C is A-B.
reduc(A*B, C)	 :- number(A), number(B), C is A*B.
reduc(A/B, C)	 :- number(A), number(B), C is A/B.

reduc(A*i+B*i, C*i)	 :- number(A), number(B), C is A+B.
reduc(A*i-B*i, C*i)	 :- number(A), number(B), C is A-B.
 
reduc(A+B, A) 	:- number(B), B =:= 0.
reduc(B+A, A) 	:- number(B), B =:= 0.
reduc(A-B, A) 	:- number(B), B =:= 0.
reduc(B-A, -A) 	:- number(B), B =:= 0.

reduc(A*B, A)	:- number(B), B =:= 1.
reduc(B*A, A) 	:- number(B), B =:= 1.
reduc(_*B, 0)	:- number(B), B =:= 0.
reduc(B*_, 0)	:- number(B), B =:= 0.

reduc(A/B, A) 	:- number(B), B =:= 1.
reduc(_/B, inf) :- number(B), B =:= 0. % this shouldnt happen at all
reduc(_/inf, 0).

% Explicit reductions
reduc(sqrt(A), B)	 	:- number(A), A >= 0, B is sqrt(A).
reduc(sqrt(A), i*B)  	:- number(A), A <  0, B is sqrt(-A).

reduc(conj(A+B), CA+CB) :- simp(conj(A), CA), simp(conj(B), CB).
reduc(conj(A*B), CA*CB) :- simp(conj(A), CA), simp(conj(B), CB).
reduc(conj(A-B), CA-CB) :- simp(conj(A), CA), simp(conj(B), CB).
reduc(conj(A/B), CA/CB) :- simp(conj(A), CA), simp(conj(B), CB).

% Radical and Complex reductions
reduc(sqrt(A*A), A).
reduc(sqrt(A**2), A).
reduc(sqrt(A)*sqrt(A), A).
reduc(sqrt(A)*sqrt(B), sqrt(A*B)).

reduc(conj(conj(A)), A).
reduc(conj(i), -i).
reduc(conj(-i), i).
reduc(conj(A), A)	 	:- number(A).

reduc(mag(A), A)	 	:- number(A), A >= 0.
reduc(mag(A), B)	 	:- number(A), A < 0, B is A * -1.
reduc(mag(B*i), R) 		:- number(B), reduc(mag(B), R).
reduc(mag(-B*i), R) 	:- number(B), reduc(mag(B), R).

reduc(mag(A + B*i), sqrt(R)) :- number(A), number(B), simp(A*A + B*B, R).
reduc(mag(B*i + A), sqrt(R)) :- number(A), number(B), simp(A*A + B*B, R).
reduc(mag(A - B*i), sqrt(R)) :- number(A), number(B), simp(A*A + B*B, R).
reduc(mag(B*i - A), sqrt(R)) :- number(A), number(B), simp(A*A + B*B, R).

% No reduction
reduc(X, X).

/* Matrix Multiplication and Transpose */
/**************************************************/

% Simplified matrix multiplier adopted from "Clause and Effect"
% though a more memory efficient version exists
% this simple version handles in this case well enough

mtx_mul(A, B, C) :- t(B, BT), h_mul_t(A, BT, C).	

% Transpose a matrix 
t([[]|_], []).
t(M, [Ci|Cn]) :- columns(M, Ci, R), t(R, Cn).


columns([], [], []).
columns([[Cii|Cin]|C], [Cii|X], [Cin|Y]) :- columns(C, X, Y).

% Helpers

% Product of all rows of A with entire B 
h_mul_t([] ,_, []).
h_mul_t([Ai|An], B, [Ci|Cn]) :- h_mul_c(Ai, B, Ci), h_mul_t(An ,B, Cn).

% Product of all "columns" of B with row A
h_mul_c(_, [], []).
h_mul_c(A, [Bi|Bn], [Ci|Cn]) :- h_prod(A, Bi, Ci), h_mul_c(A, Bn, Cn).

h_prod([], [], 0).
h_prod([Ai|An], [Bi|Bn], (X + Ai * Bi)) :- h_prod(An, Bn, X).


/* Matrices and Vectors Operations */
/**************************************************/
compose([H|T], Result) :- h_compose(T, H, Result).

% Helpers

h_compose([], ACC, ACC).

h_compose([H|T], ACC, Result) :-
	mtx_mul(ACC, H, Next_ACC),
	h_compose(T, Next_ACC, Result).

vec_to_covariant(V, Result) :- h_conjlist(V, R), Result = [R].

vec_to_contravariant([], []).
vec_to_contravariant([H|T], [[H]|Rest]) :- vec_to_contravariant(T, Rest).

% Helpers

h_conjlist([], []).
h_conjlist([H|T], [conj(H)|Rest]) :- h_conjlist(T, Rest).



/* Dirac Notation */
/**************************************************/

/*
Examples:
ket('1', X).
braket('1', [O1, O2, O3], '+').
..etc 
Operators and bases needs to be defined as shown later.
*/

h_map_to_rep(O, Total) :-
	maplist(operator, O, Replist),
	compose(Replist, Total).

ket(Psi, X) :- 
	basis(Psi, V), 
	vec_to_contravariant(V, X).

ket(O, Psi, X) :- 
	h_map_to_rep(O, O_total),
	basis(Psi, V), 
	vec_to_contravariant(V, X1),
	mtx_mul(O_total, X1, X_ns),
	simpmat(X_ns, X).

bra(Psi, X) :- 
	basis(Psi, V), 
	vec_to_covariant(V, X).

bra(Psi, O, X) :- 
	h_map_to_rep(O, O_total),
	basis(Psi, V), 
	vec_to_covariant(V, X1),
	mtx_mul(X1, O_total, X_ns),
	simpmat(X_ns, X).

braket(Phi, Psi, Result) :-
	bra(Phi, X), ket(Psi, Y),
	mtx_mul(X, Y, [[Result_ns]]),
	simp(Result_ns, Result).

braket(Phi, O, Psi, Result) :-
	bra(Phi, Bra), h_map_to_rep(O, O_total), ket(Psi, X),
	mtx_mul(O_total, X, Ket),
	mtx_mul(Bra, Ket, [[Result_ns]]),
	simp(Result_ns, Result).

ketbra(Phi, Psi, Result) :-
	ket(Phi, X), bra(Psi, Y),
	mtx_mul(X, Y, Result_ns),
	simpmat(Result_ns, Result).

ketbra(Phi, O, Psi, Result) :-
	ket(Phi, Ket), h_map_to_rep(O, O_total), bra(Psi, X),
	mtx_mul(X, O_total, Bra),
	mtx_mul(Ket, Bra, Result_ns),
	simpmat(Result_ns, Result).


/* Operators */
/**************************************************/

% 2x2 matrices
operator(hadamard, [[1/sqrt(2), 1/sqrt(2)], [1/sqrt(2), -1/sqrt(2)]]).
operator(sig_x,    [[0, 1],  [1, 0]]).
operator(sig_y,    [[0, i], [-i, 0]]).
operator(sig_z,    [[1, 0],  [0, -1]]).

% 4x4 matrices
operator(hh, 	[[1/2,  1/2,  1/2,  1/2],
				 [1/2, -1/2,  1/2, -1/2],
				 [1/2,  1/2, -1/2, -1/2],
				 [1/2, -1/2, -1/2,  1/2]]).

operator(uf_const0, [[1,0,0,0],
					 [0,1,0,0],
					 [0,0,1,0],
					 [0,0,0,1]]).

operator(uf_const1, [[0,1,0,0],
					 [1,0,0,0],
					 [0,0,0,1],
					 [0,0,1,0]]).

operator(uf_balanced_id, [[1,0,0,0],
						  [0,1,0,0],
						  [0,0,0,1],
						  [0,0,1,0]]).

operator(uf_balanced_not,  [[0,1,0,0],
							[1,0,0,0],
							[0,0,1,0],
							[0,0,0,1]]).
/* Bases */
/**************************************************/

% 1-qubit basis
basis('1', [0, 1]).
basis('0', [1, 0]).

basis('+', [1/sqrt(2), 1/sqrt(2)]).
basis('-', [1/sqrt(2), -1/sqrt(2)]).


% 2-qubit basis
basis('00', [1, 0, 0, 0]).
basis('01', [0, 1, 0, 0]).
basis('10', [0, 0, 1, 0]).
basis('11', [0, 0, 0, 1]).

/* An example for a 2qubit Deutsch Algorithm */
/**************************************************/

h_deutsch(Oracle, A, B, C, D) :-
	member(Oracle, [uf_const0, uf_const1, uf_balanced_id, uf_balanced_not]),
	ket([hh, Oracle, hh], '01', [[A_ns],[B_ns],[C_ns],[D_ns]]),
	simp(A_ns, A), simp(B_ns, B), simp(C_ns, C), simp(D_ns, D).

deutsch(Oracle, 'Extend the simplifier') :-
    h_deutsch(Oracle, _, B, _, _),
    \+ number(B).

deutsch(Oracle, constant) :-
	h_deutsch(Oracle, _, B, _, _),
	B =\= 0.

deutsch(Oracle, balanced) :-
	h_deutsch(Oracle, _, B, _, _),
	B =:= 0.

% Now query deutsch(X, Y). and see what happens.
% Also try query braket('0', [X, Y], '1', C).
