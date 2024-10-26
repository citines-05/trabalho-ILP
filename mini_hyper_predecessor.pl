%———————————————————————————————————————————————
% Learning from family relations
% prove(Goal, Hypo, Ans)
%   Ans = yes …

prove(Goal, Hypo, Answer):-
    max_proof_length(D),
    prove(Goal, Hypo, D, RestD),
    (RestD >= 0, Answer = yes		% Proved
     ;				     
     RestD < 0, Answer = maybe).	% Maybe, but it looks like inf. loop
prove(Goal, _, no).			% Otherwise goal definitely cannot be proved


%———————————————————————————————————————————————
% prove(Goal, Hypo, MaxD, RestD)

prove(G, H, D, D):-
    D <0, !.
prove([], _, D, D):- !.
prove([G1|Gs],Hypo,D0,D):-
    prove(G1,Hypo,D0,D1),
    prove(Gs,Hypo,D1,D).
prove(G,_,D,D):-
    prolog_predicate(G),
    call(G).
prove(G,Hypo,D0,D):-
    D0 =< 0, !,
    D is D0-1
    ;
    D1 is D0 - 1,
    member(Clause/Vars, Hypo),
    copy_term(Clause,[Head|Body]),
    G = Head,
    prove(Body, Hypo,D1,D).

%——————————————————————————————————————————————-——————————————-
induce(Hyp):-
    iter_deep(Hyp,0).

iter_deep(Hyp, MaxD):- 
    write('Current MaxD= '), write(MaxD), nl, 
    start_hyp(Hyp0), 
    complete(Hyp0), 
    depth_first(Hyp0, Hyp, MaxD),
    write('Depth first completed with MaxD='), write(MaxD), nl
    ; 
    NewMaxD is MaxD + 1, 
    write('Incrementing MaxD to '), write(NewMaxD), nl, 
    iter_deep(Hyp, NewMaxD).


depth_first(Hyp, Hyp, _):- 
    consistent(Hyp).
    %write('Consistent Hypothesis Found: '), write(Hyp), nl.
depth_first(Hyp0, Hyp, MaxD0):- 
    MaxD0 > 0, 
    MaxD1 is MaxD0 - 1, 
    %write('Attempting to refine hypothesis at MaxD='), write(MaxD0), nl,
    refine_hyp(Hyp0, Hyp1), 
    complete(Hyp1), 
    depth_first(Hyp1, Hyp, MaxD1).


complete(Hyp):-
    not(ex(E),				% A positive example
        once(prove(E, Hyp, Answer)),	% Prove it with Hyp
        Answer \== yes).		% possibly provable

consistent(Hyp):- 
    not(nex(E), 
        once(prove(E, Hyp, Answer)), 
        (Answer \== no -> write('Inconsistent due to: '), write(E), nl; true)).
		% possibly provable

refine_hyp(Hyp0, Hyp):- 
    write('Refining Hypothesis: '), write(Hyp0), nl,
    conc(Clauses1, [Clause0/Vars0 | Clauses2], Hyp0), 
    conc(Clauses1, [Clause/Vars | Clauses2], Hyp), 
    refine(Clause0, Vars0, Clause, Vars).
    %write('Refined Hypothesis: '), write(Hyp), nl.


refine(Clause, Args, Clause, NewArgs):-
    conc(Args1, [A | Args2], Args),
    member(A, Args2),
    conc(Args1, Args2, NewArgs).
refine(Clause,Args,NewClause, NewArgs):-
    length(Clause, L),
    max_clause_length(MaxL),
    L < MaxL,
    backliteral(Lit, Vars),
    conc(Clause,[Lit],NewClause),
    conc(Args, Vars, NewArgs).

max_proof_length(20).

max_clause_length(3).

conc([],L,L).
conc([X|T],L,[X|L1]):-
    conc(T,L,L1).

%———————————————————————————————————————————————
not(A,B,C):-
    A,
    B,
    C, !, fail.
not(_,_,_).

%———————————————————————————————————————————————
male(tom).
male(bob).
male(jim).
female(pam).
female(liz).
female(ann).
female(pat).
female(eve).

parent(pam, bob).
parent(pam, jim).
parent(tom, liz).
parent(bob, ann).
parent(bob, pat).
parent(pat, jim).
parent(pat, eve).


has_daughter(X):-
    parent(X,Y),
    female(Y).


%-----------------------------------------------
% Definition of the recursive predecessor relation
predecessor(X, Y) :- 
    parent(X, Y).
predecessor(X, Y) :- 
    parent(X, Z), 
    predecessor(Z, Y).

%-----------------------------------------------
% Backward literals for learning
backliteral(parent(X,Y), [X,Y]).
backliteral(predecessor(X,Y), [X,Y]).

% Predicates known to the system
prolog_predicate(parent(_, _)).
prolog_predicate(predecessor(_, _)).


%———————————————————————————————————————————————
% Positive examples
% ex(+Example): +Example is a positive example
ex(predecessor(pam, bob)). 
ex(predecessor(pam, jim)).
ex(predecessor(tom, ann)).
ex(predecessor(tom, jim)). 
ex(predecessor(tom, liz)).


%———————————————————————————————————————————————
% Negative examples
%nex(+Example): +Example is a 
nex(predecessor(liz, bob)). 
nex(predecessor(pat, bob)). 
nex(predecessor(pam, liz)). 
nex(predecessor(liz, jim)). 
nex(predecessor(liz, liz)).  



start_hyp([[predecessor(X1,Y1)]/[X1,Y1], [predecessor(X2,Y2)]/[X2,Y2]]).

