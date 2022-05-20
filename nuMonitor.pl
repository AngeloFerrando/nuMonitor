% Labeled transition system for LTv terms
trans(Term, Event, NewTerm) :-
    findall(Term1, trans_aux(Term, Event, Term1), NextTerms),
    %trans_aux(Term, Event, Term1),
    generate_or_term(NextTerms, Term2),
    opt(Term2, NewTerm).
trans_aux(tt, _Event, tt).
trans_aux(prop(Proposition, tt), Event, tt) :- member(Proposition, Event).
trans_aux(prop(Proposition, ff), Event, tt) :- not(member(Proposition, Event)).
trans_aux(next(Term), _Event, Term).
trans_aux(and(Term1, Term2), Event, and(Term3, Term4)) :- trans_aux(Term1, Event, Term3), trans_aux(Term2, Event, Term4).
trans_aux(or(Term1, Term2), Event, Term3) :- trans_aux(Term1, Event, Term3); trans_aux(Term2, Event, Term3).

opt(Term, OptTerm) :-
    empty_assoc(Assoc),
    opt_aux(Term, OptTerm, Assoc).
opt_aux(Term, OptTerm, Assoc) :-
    get_assoc(Term, Assoc, OptTerm), !.
opt_aux(tt, tt, _) :- !.
opt_aux(ff, ff, _) :- !.
opt_aux(prop(Event, tt), prop(Event, tt), _) :- !.
opt_aux(prop(Event, ff), prop(Event, ff), _) :- !.
opt_aux(next(Term), OptTerm, Assoc) :-
    put_assoc(next(Term), Assoc, OptTerm, Assoc1),
    opt_aux(Term, Term1, Assoc1), (Term1 == tt -> (OptTerm = tt);(OptTerm = next(Term1))), !.
opt_aux(and(Term1, Term2), OptTerm, Assoc) :-
    put_assoc(and(Term1, Term2), Assoc, OptTerm, Assoc1),
    opt_aux(Term1, OptTerm1, Assoc1), opt_aux(Term2, OptTerm2, Assoc1),
    (OptTerm1 == ff ->
        (OptTerm = ff);
        (OptTerm1 == tt ->
            (OptTerm = OptTerm2);
            (OptTerm2 == ff ->
                (OptTerm = ff);
                (OptTerm2 == tt ->
                    (OptTerm = OptTerm1);
                    (OptTerm = and(OptTerm1, OptTerm2)))))), !.
opt_aux(or(Term1, Term2), OptTerm, Assoc) :-
    put_assoc(or(Term1, Term2), Assoc, OptTerm, Assoc1),
    opt_aux(Term1, OptTerm1, Assoc1), opt_aux(Term2, OptTerm2, Assoc1),
    (OptTerm1 == ff ->
        (OptTerm = OptTerm2);
        (OptTerm1 == tt ->
            (OptTerm = tt);
            (OptTerm2 == ff ->
                (OptTerm = OptTerm1);
                (OptTerm2 == tt ->
                    (OptTerm = tt);
                    (OptTerm = or(OptTerm1, OptTerm2)))))), !.

% proof system for nu-calculus
is_satisfied(Term, Alphabet) :-
    not(is_list(Term)), !,
    empty_assoc(Assoc),
    is_satisfied([Term], Alphabet, Assoc), !.
is_satisfied(Terms, _Alphabet, Assoc) :-
    findall(Term, (member(Term, Terms), not(get_assoc(Term, Assoc, _))), []), !. 
is_satisfied(Terms, _Alphabet, _Assoc) :-
    nth0(_Index, Terms, tt),
    !.
is_satisfied(Terms, Alphabet, Assoc) :-
    nth0(Index, Terms, next(Term)), not(get_assoc(next(Term), Assoc, _)),
    !, 
    put_assoc(next(Term), Assoc, _, Assoc1),
    update(Index, Terms, Term, Terms1),
    is_satisfied(Terms1, Alphabet, Assoc1).
is_satisfied(Terms, Alphabet, Assoc) :-
    nth0(Index, Terms, and(Term1, Term2)), not(get_assoc(and(Term1, Term2), Assoc, _)),
    !, 
    put_assoc(and(Term1, Term2), Assoc, _, Assoc1), 
    update(Index, Terms, Term1, Terms1),
    update(Index, Terms, Term2, Terms2),
    is_satisfied(Terms1, Alphabet, Assoc1),
    is_satisfied(Terms2, Alphabet, Assoc1).
is_satisfied(Terms, Alphabet, Assoc) :- 
    nth0(Index, Terms, or(Term1, Term2)), not(get_assoc(or(Term1, Term2), Assoc, _)),
    !,
    put_assoc(or(Term1, Term2), Assoc, _, Assoc1),
    update(Index, Terms, Term1, Terms1),
    is_satisfied([Term2|Terms1], Alphabet, Assoc1).
is_satisfied(Terms, Alphabet, _Assoc) :- 
    !,
    findall(P, (member(P, Alphabet), member(T, Terms), trans(T, [P], _)), Props1),
    sort(Props1, Props),
    length(Alphabet, N1),
    length(Props, N2),
    N1 == N2.

% proof system using trans, but it only works for non-expansive terms
%is_all(tt, _) :- !.
%is_all(next(Term), Alphabet) :- is_all(Term, Alphabet), !.
% is_all(Term, Alphabet) :-
%     findall((Event, Term1), trans(Term, Event, Term1), NextTerms),
%     findall(Event, member((Event, _), NextTerms), Events),
%     findall(Term1, member((_, Term1), NextTerms), Terms),
%     Alphabet = Events,
%     findall(NextTerm, (member(NextTerm, Terms), not(is_all(NextTerm, Alphabet))), []).

% syntactic encoding from LTL to nu-calculus
encoding(LTL, Term) :-
    nnf(LTL, NNFLTL),
    encoding_aux(NNFLTL, Term), !. 
encoding_aux(tt, tt).
encoding_aux(ff, ff).
encoding_aux(prop(Proposition, tt), prop(Proposition, tt)).
encoding_aux(prop(Proposition, ff), prop(Proposition, ff)).
encoding_aux(next(LTL), next(Term)) :- encoding_aux(LTL, Term).
encoding_aux(and(LTL1, LTL2), and(Term1, Term2)) :- encoding_aux(LTL1, Term1), encoding_aux(LTL2, Term2).
encoding_aux(or(LTL1, LTL2), or(Term1, Term2)) :- encoding_aux(LTL1, Term1), encoding_aux(LTL2, Term2).
encoding_aux(until(LTL1, LTL2), Term) :- encoding_aux(LTL1, Term1), encoding_aux(LTL2, Term2), Term = or(Term2, and(Term1, next(Term))).
encoding_aux(release(LTL1, LTL2), Term) :- encoding_aux(LTL1, Term1), encoding_aux(LTL2, Term2), Term = and(Term2, or(Term1, next(Term))).

t(buchi(_States, _Alphabet, [], _Transitions, _FinalStates), ff) :- !.
t(buchi(States, Alphabet, InitialStates, Transitions, FinalStates), OrTerm) :-
    !, findall(NuTerm, (member(State, InitialStates), empty_assoc(A), t(State, buchi(States, Alphabet, InitialStates, Transitions, FinalStates), A, NuTerm)), NuTerms),
    generate_or_term(NuTerms, OrTerm).
t(State, buchi(_States, _Alphabet, _InitialStates, _Transitions, _FinalStates), Assoc, NuTerm) :-
	get_assoc(State, Assoc, NuTerm), !.
t(State, buchi(States, Alphabet, InitialStates, Transitions, FinalStates), Assoc, NuTerm) :-
    put_assoc(State, Assoc, NuTerm, Assoc1),
    findall((Alpha,NextState),(member(trans(State, Alpha, NextState), Transitions)),AlphaNextStates),
    bagof(AndTerm,Alpha^NextState^AlphaNextStates^AlphaTerm^AndTerm^NuTerm1^(member((Alpha, NextState), AlphaNextStates), t_alpha(Alpha, AlphaTerm), t(NextState, buchi(States, Alphabet, InitialStates, Transitions, FinalStates), Assoc1, NuTerm1), AndTerm = and(AlphaTerm, next(NuTerm1))), AndTerms),
    generate_or_term(AndTerms, NuTerm).

t_alpha(Set, NuTerm) :-
	findall(prop(Prop, V), member(prop(Prop, V), Set), Props),
    generate_and_term(Props, NuTerm).

% negation normal form of an LTL formula
nnf(LTL, NNFLTL) :- nnf(LTL, NNFLTL, tt).
nnf(globally(Term), release(ff, Term1), tt) :-
    !, nnf(Term, Term1, tt).
nnf(globally(Term), Term1, ff) :-
    !, nnf(eventually(not(Term)), Term1, tt).
nnf(eventually(Term), until(tt, Term1), tt) :-
    !, nnf(Term, Term1, tt).
nnf(eventually(Term), Term1, ff) :-
    !, nnf(globally(not(Term)), Term1, tt).
nnf(tt, tt, tt) :- !.
nnf(tt, ff, ff) :- !.
nnf(ff, ff, tt) :- !.
nnf(ff, tt, ff) :- !.
nnf(not(Term), Term1, Value) :- 
    !,
    (Value == tt ->  (NewValue = ff);(NewValue = tt)),
    nnf(Term, Term1, NewValue).
nnf(prop(Proposition, tt), prop(Proposition, tt), tt) :- !.
nnf(prop(Proposition, tt), prop(Proposition, ff), ff) :- !.
nnf(prop(Proposition, ff), prop(Proposition, ff), tt) :- !.
nnf(prop(Proposition, ff), prop(Proposition, tt), ff) :- !.
nnf(next(LTL), next(LTL1), Value) :- !, nnf(LTL, LTL1, Value).
nnf(and(LTL1, LTL2), and(LTL3, LTL4), tt) :- !, nnf(LTL1, LTL3, tt), nnf(LTL2, LTL4, tt).
nnf(and(LTL1, LTL2), or(LTL3, LTL4), ff) :- !, nnf(LTL1, LTL3, ff), nnf(LTL2, LTL4, ff).
nnf(or(LTL1, LTL2), or(LTL3, LTL4), tt) :- !, nnf(LTL1, LTL3, tt), nnf(LTL2, LTL4, tt).
nnf(or(LTL1, LTL2), and(LTL3, LTL4), ff) :- !, nnf(LTL1, LTL3, ff), nnf(LTL2, LTL4, ff).
nnf(until(LTL1, LTL2), until(LTL3, LTL4), tt) :- !, nnf(LTL1, LTL3, tt), nnf(LTL2, LTL4, tt).
nnf(until(LTL1, LTL2), release(LTL3, LTL4), ff) :- !, nnf(LTL1, LTL3, ff), nnf(LTL2, LTL4, ff).
nnf(release(LTL1, LTL2), release(LTL3, LTL4), tt) :- !, nnf(LTL1, LTL3, tt), nnf(LTL2, LTL4, tt).
nnf(release(LTL1, LTL2), until(LTL3, LTL4), ff) :- !, nnf(LTL1, LTL3, ff), nnf(LTL2, LTL4, ff).

% closure of an LTL formula
closure(tt, [tt]) :- !.
closure(ff, []) :- !.
closure(prop(Proposition, _), [prop(Proposition, tt), prop(Proposition, ff)]) :- !.
closure(not(LTL), [not(LTL), LTL, ClLTL]) :-
    !, closure(LTL, ClLTL).
closure(next(LTL), [next(LTL), not(next(LTL))|ClLTL]) :-
    !, closure(LTL, ClLTL).
closure(and(LTL1, LTL2), [and(LTL1, LTL2), not(and(LTL1, LTL2))|ClLTL]) :-
    !, closure(LTL1, ClLTL1),
    closure(LTL2, ClLTL2),
    union(ClLTL1, ClLTL2, ClLTL).
closure(or(LTL1, LTL2), [or(LTL1, LTL2), not(or(LTL1, LTL2))|ClLTL]) :-
    !, closure(LTL1, ClLTL1),
    closure(LTL2, ClLTL2),
    union(ClLTL1, ClLTL2, ClLTL).
closure(until(LTL1, LTL2), [until(LTL1, LTL2), not(until(LTL1, LTL2))|ClLTL]) :-
    !, closure(LTL1, ClLTL1),
    closure(LTL2, ClLTL2),
    union(ClLTL1, ClLTL2, ClLTL).
closure(release(LTL1, LTL2), [release(LTL1, LTL2), not(release(LTL1, LTL2))|ClLTL]) :-
    !, closure(LTL1, ClLTL1),
    closure(LTL2, ClLTL2),
    union(ClLTL1, ClLTL2, ClLTL).

% Set of maximally consistent LTL formulas, given the closure of an LTL formula
set_maximally_consistent(Closure, MaxConsistentSet) :-
    findall(C1, locally_consistent(Closure, C1), Cs), 
    findall(C1, (member(C1, Cs), member(C2, Cs), C1\=C2, subset(C1, C2)), Cs1), 
    subtract(Cs, Cs1, MaxConsistentSet).
locally_consistent(Closure, Consistent) :-
    seq_subseq(Closure, Consistent), Consistent \= [],
    findall(LTL,(member(LTL, Consistent), member(not(LTL), Consistent)), []),
    findall(P,(member(prop(P,V1), Consistent), member(prop(P,V2), Consistent), V1\==V2), []),
    findall(LTL, (member(and(LTL1, LTL2), Consistent), (not(member(LTL1, Consistent)); not(member(LTL2, Consistent)))), []),
    findall(LTL, (member(and(LTL1, LTL2), Closure), member(LTL1, Consistent), member(LTL2, Consistent), not(member(and(LTL1, LTL2), Consistent))), []),
    findall(LTL, (member(and(LTL1, LTL2), Closure), member(LTL1, Consistent), member(LTL2, Consistent), member(not(and(LTL1, LTL2)), Consistent)), []),
    findall(LTL, (member(or(LTL1, LTL2), Closure), (member(LTL1, Consistent); member(LTL2, Consistent)), not(member(or(LTL1, LTL2), Consistent))), []),
    findall(LTL, (member(or(LTL1, LTL2), Closure), (member(LTL1, Consistent); member(LTL2, Consistent)), member(not(or(LTL1, LTL2)), Consistent)), []),
    findall(LTL, (member(or(LTL1, LTL2), Consistent), not(member(LTL1, Consistent)), not(member(LTL2, Consistent))), []).

% from LTL formula to Buchi automaton
buchi_automaton(LTL, Alphabet, Buchi) :-
    nnf(LTL, NNFLTL),
    closure(NNFLTL, ClLTL),
    findall(Set, (set_maximally_consistent(ClLTL, SetOfSets), member(Set, SetOfSets)), States),
    findall(Set, (member(Set, States), member(NNFLTL, Set)), InitialStates),
    findall(until(Phi,Psi), member(until(Phi, Psi), ClLTL), Untils),
    (Untils = [] ->  (FinalStates = [States]);(findall(UntilFinals,(member(until(Phi, Psi), Untils), findall(Set1,(member(Set1, States), (member(Psi, Set1);not(member(until(Phi, Psi), Set1)))),UntilFinals)),FinalStates))),
    findall(trans(Set1, Props, Set2),(member(Set1, States), member(Set2, States), ltl_consistent(ClLTL, Set1, Set2), findall(prop(P,V), member(prop(P, V), Set1), Props)), Transitions),
    findall(Set, (member(Set, States), not(member(trans(Set, _, _), Transitions)), not(member(trans(_, _, Set), Transitions))), DeadStates),
    subtract(States, DeadStates, NewStates), 
    Buchi1 = buchi(NewStates, Alphabet, InitialStates, Transitions, FinalStates),
    degeneralise(Buchi1, DgBuchi),
 	opt_buchi(DgBuchi, Buchi).

opt_buchi(buchi(States, Alphabet, InitialStates, Transitions, FinalStates), Buchi) :-
    findall(State,(member(State, States), is_not_empty(State, buchi(States, Alphabet, InitialStates, Transitions, FinalStates))), GoodStates),
    sort(GoodStates, GoodStates1),
    intersection(InitialStates, GoodStates1, InitialStates1),
	findall(trans(S1, E, S2),(member(trans(S1, E, S2), Transitions), member(S1, GoodStates1), member(S2, GoodStates1)), Transitions1),
    sort(Transitions1, Transitions2),
    intersection(FinalStates, GoodStates1, FinalStates1),
    Buchi = buchi(GoodStates1, Alphabet, InitialStates1, Transitions2, FinalStates1).

% check if the language starting from a state of the automaton is not empty
is_not_empty(State, Buchi) :-
    is_not_empty(State, Buchi, [], 0), !.
is_not_empty(State, buchi(_States, _Alphabet, _InitialStates, _Transitions, FinalStates), SeenStates, _D) :-
    member((State, Depth), SeenStates), !,
    member((State1, Depth1), SeenStates),
    member(State1, FinalStates),
    Depth1 >= Depth, !.
is_not_empty(State, buchi(States, Alphabet, InitialStates, Transitions, FinalStates), SeenStates, D) :-
    D1 is D + 1,
    member(trans(State, _, State1), Transitions),
    is_not_empty(State1, buchi(States, Alphabet, InitialStates, Transitions, FinalStates), [(State, D1)|SeenStates], D1), !.

% from generalised buchi automaton to buchi automaton
degeneralise(buchi(States, Alphabet, InitialStates, Transitions, []), DegenBuchi) :- 
    DegenBuchi = buchi(States, Alphabet, InitialStates, Transitions, []), !.
degeneralise(buchi(States, Alphabet, InitialStates, Transitions, [FinalStates]), DegenBuchi) :- 
    DegenBuchi = buchi(States, Alphabet, InitialStates, Transitions, FinalStates), !.
degeneralise(buchi(States, Alphabet, InitialStates, Transitions, FinalStates), DegenBuchi) :- 
    FinalStates = [FinalStates1|Aux], 
    Aux = [FinalStates2|Rest],
    product(buchi(States, Alphabet, InitialStates, Transitions, FinalStates1), buchi(States, Alphabet, InitialStates, Transitions, FinalStates2), buchi(StatesP, AlphabetP, InitialStatesP, TransitionsP, FinalStatesP)),
    (Rest = [] -> (DegenBuchi = buchi(StatesP, AlphabetP, InitialStatesP, TransitionsP, FinalStatesP));(append(FinalStatesP, Rest, FinalStatesP1), Product = buchi(StatesP, AlphabetP, InitialStatesP, TransitionsP, FinalStatesP1), degeneralise(Product, DegenBuchi))).
    
% product of buchi automata
product(buchi(States1, Alphabet1, InitialStates1, Transitions1, FinalStates1), buchi(States2, Alphabet2, InitialStates2, Transitions2, FinalStates2), Product) :-
	findall((S1, S2, 1),(member(S1, States1), member(S2, States2)), StatesAux1),
    findall((S1, S2, 2),(member(S1, States1), member(S2, States2)), StatesAux2),
    union(StatesAux1, StatesAux2, States),
    findall((I1, I2, 1),(member(I1, InitialStates1), member(I2, InitialStates2)), InitialStates),
    union(Alphabet1, Alphabet2, Alphabet),
    findall((S1, F2, 2), (member(S1, States1), member(F2, FinalStates2)), FinalStates),
    findall((S3, S4, I),(member((S1,S2,1), States), member(trans(S1, E, S3), Transitions1), member(trans(S2, E, S4), Transitions2), (member(S1, FinalStates1) -> (I = 2);(I = 1))), TransitionsAux1),
    findall((S3, S4, I),(member((S1,S2,2), States), member(trans(S1, E, S3), Transitions1), member(trans(S2, E, S4), Transitions2), (member(S2, FinalStates2) -> (I = 1);(I = 2))), TransitionsAux2),
    union(TransitionsAux1, TransitionsAux2, Transitions),
    Product = buchi(States, Alphabet, InitialStates, Transitions, FinalStates).


% LTL consistency for buchi automaton's states
ltl_consistent(Closure, Set1, Set2) :-
    findall(Phi, (member(next(Phi), Set1), not(member(Phi, Set2))), []),
    findall(Phi, (member(next(Phi), Closure), member(Phi, Set2), not(member(next(Phi), Set1))), []),
    findall(Phi, (member(until(Phi, Psi), Set1), (not(member(Psi, Set1)), (not(member(Phi, Set1)); not(member(until(Phi, Psi), Set2))))), []),
    findall(Phi, (member(until(Phi, Psi), Closure), (member(Psi, Set1); (member(Phi, Set1), member(until(Phi, Psi), Set2))), not(member(until(Phi, Psi), Set1))), []),
    findall(Phi, (member(release(Phi, Psi), Set1), (not(member(and(Phi, Psi), Set1)), (not(member(Psi, Set1)); not(member(release(Phi, Psi), Set2))))), []),
    findall(Phi, (member(release(Phi, Psi), Closure), (member(and(Phi, Psi), Set1); (member(Psi, Set1), member(release(Phi, Psi), Set2))), not(member(release(Phi, Psi), Set1))), []).    

% 3-valued monitor
monitor3(Term, Alphabet, [], tt) :-
    is_satisfied(Term, Alphabet), !.
monitor3(_Term, _Alphabet, [], ?) :- !.
monitor3(Term, _Alphabet, [Event|_Trace], ff) :-
    not(trans(Term, Event, _NewTerm)), !.
monitor3(Term, Alphabet, [Event|Trace], Verdict) :-
	trans(Term, Event, NewTerm1),
    monitor3(NewTerm1, Alphabet, Trace, Verdict).

% 6-valued monitor
monitor6(syntactic, LTL, Alphabet, Trace, Verdict) :-
    nnf(LTL, NNFLTL1),
    nnf(not(LTL), NNFLTL2),
    encoding(NNFLTL1, NuTerm1),
    encoding(NNFLTL2, NuTerm2),
    monitor3(NuTerm1, Alphabet, Trace, VerdictSafe),
    monitor3(NuTerm2, Alphabet, Trace, VerdictCoSafe),
    compute_verdict(VerdictSafe, VerdictCoSafe, Verdict), !.
monitor6(semantic, LTL, Alphabet, Trace, Verdict) :-
    nnf(LTL, NNFLTL1),
    nnf(not(LTL), NNFLTL2),
    buchi_automaton(NNFLTL1, Alphabet, Buchi1),
    buchi_automaton(NNFLTL2, Alphabet, Buchi2), 
    t(Buchi1, NuTerm1),
    t(Buchi2, NuTerm2),
    %findall(VerdictSafe, monitor3(NuTerm1, Alphabet, Trace, VerdictSafe), AllVerdictSafe),
    %merge_verdicts(AllVerdictSafe, VerdictSafe), writeln(AllVerdictSafe),
    monitor3(NuTerm1, Alphabet, Trace, VerdictSafe),
    %findall(VerdictCoSafe, monitor3(NuTerm2, Alphabet, Trace, VerdictCoSafe), AllVerdictCoSafe),
    %merge_verdicts(AllVerdictCoSafe, VerdictCoSafe), writeln(AllVerdictCoSafe),
    monitor3(NuTerm2, Alphabet, Trace, VerdictCoSafe),
    compute_verdict(VerdictSafe, VerdictCoSafe, Verdict), !.
monitor6(direct, NuTermOver, NuTermUnder, Alphabet, Trace, Verdict) :-
    is_satisfied(or(NuTermOver,NuTermUnder), Alphabet), 
    monitor3(NuTermOver, Alphabet, Trace, VerdictSafe),
    monitor3(NuTermUnder, Alphabet, Trace, VerdictCoSafe),
    compute_verdict(VerdictSafe, VerdictCoSafe, Verdict), !.

% auxiliary predicates

update(0, [_E|Es], E1, [E1|Es]) :- !.
update(I, [E|Es], E1, [E|Res]) :-
    I1 is I-1,
    update(I1, Es, E1, Res).

compute_verdict(_, ff, tt).
compute_verdict(ff, _, ff).
compute_verdict(tt, tt, x).
compute_verdict(tt, ?, ?(tt)).
compute_verdict(?, tt, ?(ff)).
compute_verdict(?, ?, ?).

merge_verdicts(Verdicts, tt) :-
    member(tt, Verdicts), !.
merge_verdicts(Verdicts, ff) :-
    findall(V,(member(V, Verdicts), V \= ff),[]), !.
merge_verdicts(Verdicts, ?(tt)) :-
    member(?(tt), Verdicts), !.
merge_verdicts(Verdicts, ?(ff)) :-
    member(?(ff), Verdicts), !.
merge_verdicts(_Verdicts, ?) :- !.

%merge_verdicts(Verdicts, Verdict) :-
%    merge_verdicts(Verdicts, Verdict, ff).
%merge_verdicts([tt|_], tt, _) :- !.
%merge_verdicts([ff|Verdicts], Verdict, CurrentVerdict) :- 
%    !, merge_verdicts(Verdicts, Verdict, CurrentVerdict).
%merge_verdicts([?|Verdicts], Verdict, CurrentVerdict) :- !, merge_verdicts(Verdicts, Verdict, CurrentVerdict).
%merge_verdicts([?(tt)|Verdicts], Verdict, _CurrentVerdict) :- !, merge_verdicts(Verdicts, Verdict, ?(tt)).
%merge_verdicts([?(ff)|Verdicts], Verdict, _CurrentVerdict) :- !, merge_verdicts(Verdicts, Verdict, ?(ff)).
%merge_verdicts([x|Verdicts], Verdict, _CurrentVerdict) :- !, merge_verdicts(Verdicts, Verdict, x).
%merge_verdicts([], Verdict, Verdict).

seq_subseq([], []).
seq_subseq([_|Es], Fs) :-
   seq_subseq(Es, Fs).
seq_subseq([E|Es], [E|Fs]) :-
   seq_subseq(Es, Fs).

generate_and_term([Term], Term) :- !.
generate_and_term([Term|Terms], and(Term, NuTerm)) :-
    !, generate_and_term(Terms, NuTerm).
generate_or_term([Term], Term) :- !.
generate_or_term([Term|Terms], or(Term, NuTerm)) :-
    !, generate_or_term(Terms, NuTerm).

