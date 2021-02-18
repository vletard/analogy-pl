test :-
  string_chars("Une phrase", A),
  string_chars("Une proposition", B),
  string_chars("Des phrases", C),
  sequence_equation(A, B, C, Solution, [optimize(est_size)]),
  Solution = solution(output(Output), Metric, Factors),
  string_chars(OutputStr, Output),
  format('~p -> ~p~n', [Metric, OutputStr]),
  print_factors(Factors),
  true.

get_assoc_default(Key, Assoc, Value, _) :-
    get_assoc(Key, Assoc, Value),
    !.
get_assoc_default(_, _, Default, Default).

sequence_equation(A, B, C, Solution, Options) :-
  % sequences setup
  compound_name_arguments(SeqA, seq, A),
  compound_name_arguments(SeqB, seq, B),
  compound_name_arguments(SeqC, seq, C),
  compound_name_arity(SeqA, seq, NA),
  compound_name_arity(SeqB, seq, NB),
  compound_name_arity(SeqC, seq, NC),

  % checking options
  (is_list(Options) ; Options = []),
  foreach(member(optimize(Metric_), Options), Metric = Metric_),
  (
    Metric == degree, !, Val0 = 1 ;
    Metric == size, !, Val0 = 0 ;
    Metric == est_size, max_list([NA, NB, NC], Val0)
  ),
  compound_name_arguments(Init, Metric, [Val0]),

  % assoc setup
  empty_assoc(Empty),
  Cursor = coord(0,0,0),
  put_assoc(Cursor, Empty, [factorization([[]],[[]],0,0,_)], SolutionAssoc),
  put_assoc(Init, Empty, SolutionAssoc, Register),
  process_next_partial(((SeqA, SeqB, SeqC), (NA, NB, NC)),
                       Solution,
                       Init,
                       (Empty, Register)).

process_next_partial(Sequences, Solution, Current, (Explored, Register)) :-
  get_assoc(Current, Register, SolutionAssoc),
  gen_assoc(Coord, SolutionAssoc, FactorizationList),
  member(Factorization, FactorizationList),
  \+ get_assoc(Factorization, Explored, _),
  !,
  put_assoc(Factorization, Explored, true, Explored1),
  (Coord = coord(I, J, K), Sequences = (_, (I, J, K)) ->
    ( % the factorization is complete
      Solution = solution(output(Output), Current, FormattedFactorization),
      format_factorization(Factorization, FormattedFactorization, Output)
      ;
      process_next_partial(Sequences, Solution, Current, (Explored1, Register))
    )
    ;
    % not complete
    findall((Coord1, Factorization1, Metric1), explore(Sequences,
                                 Coord, Factorization, Current,
                                 Coord1, Factorization1, Metric1), Additions),
    foldl(add_factorization, Additions, Register, Register1),
    process_next_partial(Sequences, Solution, Current, (Explored1, Register1))
  ).

process_next_partial(Sequences, Solution, Current, (Explored, Register)) :-
  del_assoc(Current, Register, _, Register1),
  gen_assoc(_, Register1, _), % still more than one key on the metric ordered
  !,
  compound_name_arguments(Current, Metric, [N]),
  N1 is N + 1,
  compound_name_arguments(Next, Metric, [N1]),
  % displaying the number of explored partial factorizations
  aggregate_all(count, gen_assoc(_, Explored, _), Size),
  format('~p: ~g active paths.~n', [Current, Size]),
  
  empty_assoc(Empty),
  process_next_partial(Sequences, Solution, Next, (Empty, Register1)).

explore(((A, B, _), _), coord(I, J, K), Factorization, degree(D), coord(I_, J_, K), Factorization1, degree(D1)) :-
  I_ is I + 1,
  J_ is J + 1,
  arg(I_, A, Item),
  arg(J_, B, Item),
  Factorization = factorization(LA, LD, _, _, crossed),
  Factorization1 = factorization([[Item]|LA], [[]|LD], 1, 0, straight),
  D1 is D + 1.
explore(((A, B, _), _), coord(I, J, K), Factorization, degree(D), coord(I_, J_, K), Factorization1, degree(D)) :-
  I_ is I + 1,
  J_ is J + 1,
  arg(I_, A, Item),
  arg(J_, B, Item),
  Factorization = factorization([FA|LA], LD, SA, SD, straight),
  SA_ is SA + 1,
  Factorization1 = factorization([[Item|FA]|LA], LD, SA_, SD, straight).
explore(((_, _, C), _), coord(I, J, K), Factorization, degree(D), coord(I, J, K_), Factorization1, degree(D1)) :-
  K_ is K + 1,
  arg(K_, C, Item),
  Factorization = factorization(LA, LD, _, _, crossed),
  Factorization1 = factorization([[]|LA], [[Item]|LD], 0, 1, straight),
  D1 is D + 1.
explore(((_, _, C), _), coord(I, J, K), Factorization, degree(D), coord(I, J, K_), Factorization1, degree(D)) :-
  K_ is K + 1,
  arg(K_, C, Item),
  Factorization = factorization(LA, [FD|LD], SA, SD, straight),
  SD_ is SD + 1,
  Factorization1 = factorization(LA, [[Item|FD]|LD], SA, SD_, straight).
explore(((A, _, C), _), coord(I, J, K), Factorization, degree(D), coord(I_, J, K_), Factorization1, degree(D1)) :-
  I_ is I + 1,
  K_ is K + 1,
  arg(I_, A, Item),
  arg(K_, C, Item),
  Factorization = factorization(LA, LD, _, _, straight),
  Factorization1 = factorization([[Item]|LA], [[]|LD], 1, 0, crossed),
  D1 is D + 1.
explore(((A, _, C), _), coord(I, J, K), Factorization, degree(D), coord(I_, J, K_), Factorization1, degree(D)) :-
  I_ is I + 1,
  K_ is K + 1,
  arg(I_, A, Item),
  arg(K_, C, Item),
  Factorization = factorization([FA|LA], LD, SA, SD, crossed),
  SA_ is SA + 1,
  Factorization1 = factorization([[Item|FA]|LA], LD, SA_, SD, crossed).
explore(((_, B, _), _), coord(I, J, K), Factorization, degree(D), coord(I, J_, K), Factorization1, degree(D1)) :-
  J_ is J + 1,
  arg(J_, B, Item),
  Factorization = factorization(LA, LD, _, _, straight),
  Factorization1 = factorization([[]|LA], [[Item]|LD], 0, 1, crossed),
  D1 is D + 1.
explore(((_, B, _), _), coord(I, J, K), Factorization, degree(D), coord(I, J_, K), Factorization1, degree(D)) :-
  J_ is J + 1,
  arg(J_, B, Item),
  Factorization = factorization(LA, [FD|LD], SA, SD, crossed),
  SD_ is SD + 1,
  Factorization1 = factorization(LA, [[Item|FD]|LD], SA, SD_, crossed).

explore(((A, B, _), _), coord(I, J, K), Factorization, size(S), coord(I_, J_, K), Factorization1, size(S1)) :-
  I_ is I + 1,
  J_ is J + 1,
  arg(I_, A, Item),
  arg(J_, B, Item),
  Factorization = factorization(LA, LD, _, _, crossed),
  Factorization1 = factorization([[Item]|LA], [[]|LD], 1, 0, straight),
  S1 is S + 1.
explore(((A, B, _), _), coord(I, J, K), Factorization, size(S), coord(I_, J_, K), Factorization1, size(S1)) :-
  I_ is I + 1,
  J_ is J + 1,
  arg(I_, A, Item),
  arg(J_, B, Item),
  Factorization = factorization([FA|LA], LD, SA, SD, straight),
  SA_ is SA + 1,
  Factorization1 = factorization([[Item|FA]|LA], LD, SA_, SD, straight),
  (SA < SD -> S1 is S ; S1 is S + 1).
explore(((_, _, C), _), coord(I, J, K), Factorization, size(S), coord(I, J, K_), Factorization1, size(S1)) :-
  K_ is K + 1,
  arg(K_, C, Item),
  Factorization = factorization(LA, LD, _, _, crossed),
  Factorization1 = factorization([[]|LA], [[Item]|LD], 0, 1, straight),
  S1 is S + 1.
explore(((_, _, C), _), coord(I, J, K), Factorization, size(S), coord(I, J, K_), Factorization1, size(S1)) :-
  K_ is K + 1,
  arg(K_, C, Item),
  Factorization = factorization(LA, [FD|LD], SA, SD, straight),
  SD_ is SD + 1,
  Factorization1 = factorization(LA, [[Item|FD]|LD], SA, SD_, straight),
  (SA > SD -> S1 is S ; S1 is S + 1).
explore(((A, _, C), _), coord(I, J, K), Factorization, size(S), coord(I_, J, K_), Factorization1, size(S1)) :-
  I_ is I + 1,
  K_ is K + 1,
  arg(I_, A, Item),
  arg(K_, C, Item),
  Factorization = factorization(LA, LD, _, _, straight),
  Factorization1 = factorization([[Item]|LA], [[]|LD], 1, 0, crossed),
  S1 is S + 1.
explore(((A, _, C), _), coord(I, J, K), Factorization, size(S), coord(I_, J, K_), Factorization1, size(S1)) :-
  I_ is I + 1,
  K_ is K + 1,
  arg(I_, A, Item),
  arg(K_, C, Item),
  Factorization = factorization([FA|LA], LD, SA, SD, crossed),
  SA_ is SA + 1,
  Factorization1 = factorization([[Item|FA]|LA], LD, SA_, SD, crossed),
  (SA < SD -> S1 is S ; S1 is S + 1).
explore(((_, B, _), _), coord(I, J, K), Factorization, size(S), coord(I, J_, K), Factorization1, size(S1)) :-
  J_ is J + 1,
  arg(J_, B, Item),
  Factorization = factorization(LA, LD, _, _, straight),
  Factorization1 = factorization([[]|LA], [[Item]|LD], 0, 1, crossed),
  S1 is S + 1.
explore(((_, B, _), _), coord(I, J, K), Factorization, size(S), coord(I, J_, K), Factorization1, size(S1)) :-
  J_ is J + 1,
  arg(J_, B, Item),
  Factorization = factorization(LA, [FD|LD], SA, SD, crossed),
  SD_ is SD + 1,
  Factorization1 = factorization(LA, [[Item|FD]|LD], SA, SD_, crossed),
  (SA > SD -> S1 is S ; S1 is S + 1).

explore(((A, B, _), (NA, NB, NC)),
        coord(I, J, K), Factorization, est_size(S),
        coord(I_, J_, K), Factorization1, est_size(S1)) :-
  I_ is I + 1,
  J_ is J + 1,
  arg(I_, A, Item),
  arg(J_, B, Item),
  Factorization = factorization(LA, LD, _, _, crossed),
  Factorization1 = factorization([[Item]|LA], [[]|LD], 1, 0, straight),
  max_list([NA-I,NB-J,NC-K], PrevRemain),
  max_list([NA-I_,NB-J_,NC-K], NewRemain),
  DeltaR = NewRemain - PrevRemain,
  S1 is S + 1 + DeltaR.
explore(((A, B, _), (NA, NB, NC)),
        coord(I, J, K), Factorization, est_size(S),
        coord(I_, J_, K), Factorization1, est_size(S1)) :-
  I_ is I + 1,
  J_ is J + 1,
  arg(I_, A, Item),
  arg(J_, B, Item),
  Factorization = factorization([FA|LA], LD, SA, SD, straight),
  SA_ is SA + 1,
  Factorization1 = factorization([[Item|FA]|LA], LD, SA_, SD, straight),
  max_list([NA-I,NB-J,NC-K], PrevRemain),
  max_list([NA-I_,NB-J_,NC-K], NewRemain),
  DeltaR = NewRemain - PrevRemain,
  (SA < SD -> S1 is S + DeltaR ; S1 is S + 1 + DeltaR).
explore(((_, _, C), (NA, NB, NC)),
        coord(I, J, K), Factorization, est_size(S),
        coord(I, J, K_), Factorization1, est_size(S1)) :-
  K_ is K + 1,
  arg(K_, C, Item),
  Factorization = factorization(LA, LD, _, _, crossed),
  Factorization1 = factorization([[]|LA], [[Item]|LD], 0, 1, straight),
  max_list([NA-I,NB-J,NC-K], PrevRemain),
  max_list([NA-I,NB-J,NC-K_], NewRemain),
  DeltaR = NewRemain - PrevRemain,
  S1 is S + 1 + DeltaR.
explore(((_, _, C), (NA, NB, NC)),
        coord(I, J, K), Factorization, est_size(S),
        coord(I, J, K_), Factorization1, est_size(S1)) :-
  K_ is K + 1,
  arg(K_, C, Item),
  Factorization = factorization(LA, [FD|LD], SA, SD, straight),
  SD_ is SD + 1,
  Factorization1 = factorization(LA, [[Item|FD]|LD], SA, SD_, straight),
  max_list([NA-I,NB-J,NC-K], PrevRemain),
  max_list([NA-I,NB-J,NC-K_], NewRemain),
  DeltaR = NewRemain - PrevRemain,
  (SA > SD -> S1 is S + DeltaR ; S1 is S + 1 + DeltaR).
explore(((A, _, C), (NA, NB, NC)),
        coord(I, J, K), Factorization, est_size(S),
        coord(I_, J, K_), Factorization1, est_size(S1)) :-
  I_ is I + 1,
  K_ is K + 1,
  arg(I_, A, Item),
  arg(K_, C, Item),
  Factorization = factorization(LA, LD, _, _, straight),
  Factorization1 = factorization([[Item]|LA], [[]|LD], 1, 0, crossed),
  max_list([NA-I,NB-J,NC-K], PrevRemain),
  max_list([NA-I_,NB-J,NC-K_], NewRemain),
  DeltaR = NewRemain - PrevRemain,
  S1 is S + 1 + DeltaR.
explore(((A, _, C), (NA, NB, NC)),
        coord(I, J, K), Factorization, est_size(S),
        coord(I_, J, K_), Factorization1, est_size(S1)) :-
  I_ is I + 1,
  K_ is K + 1,
  arg(I_, A, Item),
  arg(K_, C, Item),
  Factorization = factorization([FA|LA], LD, SA, SD, crossed),
  SA_ is SA + 1,
  Factorization1 = factorization([[Item|FA]|LA], LD, SA_, SD, crossed),
  max_list([NA-I,NB-J,NC-K], PrevRemain),
  max_list([NA-I_,NB-J,NC-K_], NewRemain),
  DeltaR = NewRemain - PrevRemain,
  (SA < SD -> S1 is S + DeltaR ; S1 is S + 1 + DeltaR).
explore(((_, B, _), (NA, NB, NC)),
        coord(I, J, K), Factorization, est_size(S),
        coord(I, J_, K), Factorization1, est_size(S1)) :-
  J_ is J + 1,
  arg(J_, B, Item),
  Factorization = factorization(LA, LD, _, _, straight),
  Factorization1 = factorization([[]|LA], [[Item]|LD], 0, 1, crossed),
  max_list([NA-I,NB-J,NC-K], PrevRemain),
  max_list([NA-I,NB-J_,NC-K], NewRemain),
  DeltaR = NewRemain - PrevRemain,
  S1 is S + 1 + DeltaR.
explore(((_, B, _), (NA, NB, NC)),
        coord(I, J, K), Factorization, est_size(S),
        coord(I, J_, K), Factorization1, est_size(S1)) :-
  J_ is J + 1,
  arg(J_, B, Item),
  Factorization = factorization(LA, [FD|LD], SA, SD, crossed),
  SD_ is SD + 1,
  Factorization1 = factorization(LA, [[Item|FD]|LD], SA, SD_, crossed),
  max_list([NA-I,NB-J,NC-K], PrevRemain),
  max_list([NA-I,NB-J_,NC-K], NewRemain),
  DeltaR = NewRemain - PrevRemain,
  (SA > SD -> S1 is S + DeltaR ; S1 is S + 1 + DeltaR).

add_factorization((Coord, Factorization, Metric), Register, Register1) :-
  empty_assoc(Empty),
  get_assoc_default(Metric, Register, SolutionAssoc, Empty),
  get_assoc_default(Coord, SolutionAssoc, FactorizationList, []),
  ord_add_element(FactorizationList, Factorization, FactorizationList1),
  put_assoc(Coord, SolutionAssoc, FactorizationList1, SolutionAssoc1),
  put_assoc(Metric, Register, SolutionAssoc1, Register1).

format_factorization(ReverseFactorization, Factorization, Output) :-
  format_factorization(ReverseFactorization, factorization([],[], _), Factorization, [], Output).
format_factorization(factorization([], [], _, _, Type), Factorization, Factorization, Output, Output) :-
  Type = crossed, Factorization = factorization(_, _, straight)
  ;
  Type = straight, Factorization = factorization(_, _, crossed).
format_factorization(factorization([FA|LA], [FD|LD], _, _, Type), factorization(LAAcc, LDAcc, _), Factorization, OutputAcc, Output) :-
  reverse(FA, AF),
  reverse(FD, DF),
  append(DF, OutputAcc, OutputAcc1),
  (Type = straight, Type_ = crossed ; Type = crossed, Type_ = straight),
  format_factorization(factorization(LA, LD, _, _, Type_), factorization([AF|LAAcc], [DF|LDAcc], _), Factorization, OutputAcc1, Output).

print_factors(factorization(LA, LD, Type)) :-
  print_factors(LA, LD, Type, "", "", "", "").
print_factors([], [], _, LineA, LineB, LineC, LineD) :-
  format('~s~n~s~n~s~n~s~n', [LineA, LineB, LineC, LineD]).
print_factors([FA|LA], [FD|LD], Type, LineA, LineB, LineC, LineD) :-
  length(FA, LenA),
  length(FD, LenD),
  fill(FA, LenD, FA_filled),
  fill(FD, LenA, FD_filled),
  append(FA_filled, ['|'], FA_),
  append(FD_filled, ['|'], FD_),
  string_chars(StrA, FA_),
  string_chars(StrD, FD_),
  string_concat(LineA, StrA, LineA_),
  string_concat(LineD, StrD, LineD_),
  (
    Type = straight,
    string_concat(LineB, StrA, LineB_),
    string_concat(LineC, StrD, LineC_),
    NextType = crossed
    ;
    Type = crossed,
    string_concat(LineC, StrA, LineC_),
    string_concat(LineB, StrD, LineB_),
    NextType = straight
  ),
  print_factors(LA, LD, NextType, LineA_, LineB_, LineC_, LineD_).

fill(L, N, L) :- N =< 0, !.
fill([], N, [' '|L]) :- N_ is N - 1, fill([], N_, L).
fill([E|T], N, [E|L]) :- N_ is N - 1, fill(T, N_, L).
