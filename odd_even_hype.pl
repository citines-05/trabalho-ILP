% --------------------------------------------------------------
% Learning odd/even length lists with cycle detection

prove(Goal, Hypo, Answer) :-
    max_proof_length(D),
    prove(Goal, Hypo, D, RestD),
    (RestD >= 0 -> Answer = yes       % Proved
    ; RestD < 0 -> Answer = maybe).    % Maybe, but it looks like inf. loop
prove(_, _, no).                      % Otherwise goal definitely cannot be proved

% --------------------------------------------------------------
% prove(Goal, Hypo, MaxD, RestD)

prove(_, _, D, D) :-
    D < 0, !.
prove([], _, D, D) :- !.
prove([G1 | Gs], Hypo, D0, D) :-
    prove(G1, Hypo, D0, D1),
    prove(Gs, Hypo, D1, D).
prove(G, _, D, D) :-
    prolog_predicate(G),
    call(G).
prove(G, Hypo, D0, D) :-
    D0 > 0,
    D1 is D0 - 1,
    member(Clause/Vars, Hypo),
    copy_term(Clause, [Head | Body]),
    G = Head,
    prove(Body, Hypo, D1, D).

% --------------------------------------------------------------
% induce(Hyp) with progress display and cycle limit

induce(Hyp) :-
    max_refinements(MaxR),
    iter_deep(Hyp, 0, MaxR).

iter_deep(Hyp, MaxD, MaxR) :-
    write('Max Depth: '), write(MaxD), nl,
    start_hyp(Hyp0),
    complete(Hyp0),
    depth_first(Hyp0, Hyp, MaxD, MaxR)
    ;
    NewMaxD is MaxD + 1,
    iter_deep(Hyp, NewMaxD, MaxR).

depth_first(Hyp, Hyp, _, _) :-
    consistent(Hyp),
    write('Consistent hypothesis found: '), write(Hyp), nl.
depth_first(Hyp0, Hyp, MaxD0, MaxR) :-
    MaxD0 > 0,
    MaxD1 is MaxD0 - 1,
    MaxR > 0,
    refine_hyp(Hyp0, Hyp1),
    NewMaxR is MaxR - 1,
    display_hypothesis_progress(Hyp1),
    complete(Hyp1),
    depth_first(Hyp1, Hyp, MaxD1, NewMaxR).

% Display progress of hypothesis refinement
display_hypothesis_progress(Hyp) :-
    findall(E, ex(E), PosExamples),
    findall(E, nex(E), NegExamples),
    length(PosExamples, TotalPos),
    length(NegExamples, TotalNeg),
    length(Hyp, CurrentHyp),
    write('Current Hypothesis: '), write(Hyp), nl,
    write('Total Positive Examples: '), write(TotalPos), nl,
    write('Total Negative Examples: '), write(TotalNeg), nl,
    write('Current Hypothesis Count: '), write(CurrentHyp), nl.

complete(Hyp) :-
    \+ (ex(E),
    once(prove(E, Hyp, Answer)),
    Answer \== yes).

consistent(Hyp) :-
    \+ (nex(E),
    once(prove(E, Hyp, Answer)),
    Answer \== no).

refine_hyp(Hyp0, Hyp) :-
    conc(Clauses1, [Clause0/Vars0 | Clauses2], Hyp0),
    conc(Clauses1, [Clause/Vars | Clauses2], Hyp),
    refine(Clause0, Vars0, Clause, Vars).

refine(Clause, Args, Clause, NewArgs) :-
    conc(Args1, [A | Args2], Args),
    member(A, Args2),
    conc(Args1, Args2, NewArgs).
refine(Clause, Args, NewClause, NewArgs) :-
    length(Clause, L),
    max_clause_length(MaxL),
    L < MaxL,
    backliteral(Lit, Vars),
    conc(Clause, [Lit], NewClause),
    conc(Args, Vars, NewArgs).

% Configurações
max_proof_length(10).
max_clause_length(3).
max_refinements(20).  % Limita o número de refinamentos

conc([], L, L).
conc([X | T], L, [X | L1]) :-
    conc(T, L, L1).

% --------------------------------------------------------------
% Background knowledge: base and recursive cases for odd and even
even([]).
even([_, _ | T]) :-
    even(T).

odd([_ | T]) :-
    even(T).

% --------------------------------------------------------------
% Define backliterals for odd and even
backliteral(even(L), [L]).
backliteral(odd(L), [L]).

prolog_predicate(even(_)).
prolog_predicate(odd(_)).

% --------------------------------------------------------------
% Positive examples for learning
ex(even([])).
ex(even([a, b])).
ex(even([a, b, c, d])).
ex(odd([a])).
ex(odd([a, b, c])).

% Negative examples for learning
nex(even([a])).
nex(even([a, b, c])).
nex(odd([])).
nex(odd([a, b])).

% Starting hypothesis
start_hyp([[even(L)]/[L], [odd(L)]/[L]]).