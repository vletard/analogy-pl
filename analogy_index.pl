main :-
  string_chars("Une phrase", A),
  string_chars("Une proposition", B),
  string_chars("Des phrases", C),
%  string_chars("a", A),
%  string_chars("a", B),
%  string_chars("b", C),
%  string_chars("", A),
%  string_chars("", B),
%  string_chars("", C),
  sequence_equation(A, B, C, Solution, [optimize(degree)]),
  Solution = solution(output(Output), Metric, Factors),
  string_chars(Output1, Output),
  Solution1 = solution(output(Output1), Metric, Factors),
  format('~p~n', [Solution1]).

get_assoc_default(Key, Assoc, Value, _) :-
    get_assoc(Key, Assoc, Value),
    !.
get_assoc_default(_, _, Default, Default).

sequence_equation(A, B, C, Solution, Options) :-
  (is_list(Options) ; Options = []),
  foreach(member(optimize(Metric_), Options), Metric = Metric_),
  (Metric = degree, !, Init = degree(1) ; Metric = size, Init = size(0)),
  compound_name_arguments(SeqA, seq, A),
  compound_name_arguments(SeqB, seq, B),
  compound_name_arguments(SeqC, seq, C),
  compound_name_arity(SeqA, seq, NA),
  compound_name_arity(SeqB, seq, NB),
  compound_name_arity(SeqC, seq, NC),
  empty_assoc(Empty),
  Cursor = coord(0,0,0),
  put_assoc(Cursor, Empty, solution(
                             Init,
                             [factorization([],[],0,0,_)]
                           ), Matrix),
  put_assoc(Init, Empty, [Cursor], Ordered),
  process_next_partial(((SeqA, SeqB, SeqC), (NA, NB, NC)), Solution, Init, (Empty, Ordered, Matrix)).

process_next_partial(Sequences, Solution, Current, (Explored, Ordered, Matrix)) :-
  get_assoc(Current, Ordered, CoordList),
  member(Coord, CoordList), % TODO avoid unnecessary steps by including a memory
  get_assoc(Coord, Matrix, solution(Metric, Factorizations)),
  member(Factorization, Factorizations),
  \+ get_assoc(Factorization, Explored, _),
  !,
  process_partial(Sequences, Solution, Current, (Explored, Ordered, Matrix), Coord, Factorization, Metric).

process_next_partial(Sequences, Solution, Current, (Explored, Ordered, Matrix)) :-
  clear_indices(Current, Explored, Ordered, Matrix, Ordered1, Matrix1),
  assoc_to_keys(Ordered, [_|_]), % still more than one key on the metric ordered
  compound_name_arguments(Current, Metric, [N]),
  N1 is N + 1,
  compound_name_arguments(Next, Metric, [N1]),
  empty_assoc(Empty),
  process_next_partial(Sequences, Solution, Next, (Empty, Ordered1, Matrix1)).

process_partial((_, (I, J, K)), Solution, _, _, coord(I, J, K), ReverseFactorization, Metric) :-
  Solution = solution(output(Output), Metric, Factorization),
  format_factorization(ReverseFactorization, Factorization, Output).
process_partial(Sequences, Solution, Current, (Explored, Ordered, Matrix), Coord, Factorization, Metric) :-
  explore(Sequences, Coord, Factorization, Metric, Ordered, Matrix, Ordered1, Matrix1),
  !,
  put_assoc(Factorization, Explored, true, Explored1),
  process_partial(Sequences, Solution, Current, (Explored1, Ordered1, Matrix1), Coord, Factorization, Metric).
process_partial(Sequences, Solution, Current, (Explored, Ordered, Matrix), Coord, Factorization, Metric) :-
  process_next_partial(Sequences, Solution, Current, (Explored1, Ordered1, Matrix1)).

clear_indices(Current, Explored, Ordered, Matrix, Ordered1, Matrix1) :-
  del_assoc(Current, Ordered, CoordList, Ordered1),
  clear_indices(Explored, CoordList, Matrix, Matrix1).
clear_indices(_, [], Matrix, Matrix).
clear_indices(Explored, [Coord|CoordList], Matrix, Matrix1) :-
  del_assoc(Coord, Matrix, solution(_, Factorizations), Matrix_),
  forall((member(Factorization, Factorizations), \+ get_assoc(Factorization, Explored, true)), throw('Inconsistent index state.')),
  clear_indices(Explored, CoordList, Matrix_, Matrix1).


explore(((A, B, _), _), coord(I, J, K), Factorization, degree(D), Ordered, Matrix, Ordered1, Matrix1) :-
  I_ is I + 1,
  J_ is J + 1,
  arg(I_, A, Item),
  arg(J_, B, Item),
  Factorization = factorization(LA, LD, _, _, crossed),
  Factorization1 = factorization([[Item]|LA], [[]|LD], 1, 0, straight),
  D1 is D + 1,
  add_factorization(coord(I_, J_, K), Factorization1, degree(D1), Ordered, Matrix, Ordered1, Matrix1).
explore(((A, B, _), _), coord(I, J, K), Factorization, degree(D), Ordered, Matrix, Ordered1, Matrix1) :-
  I_ is I + 1,
  J_ is J + 1,
  arg(I_, A, Item),
  arg(J_, B, Item),
  Factorization = factorization([FA|LA], LD, SA, SD, straight),
  SA_ is SA + 1,
  Factorization1 = factorization([[Item|FA]|LA], LD, SA_, SD, straight),
  add_factorization(coord(I_, J_, K), Factorization1, degree(D), Ordered, Matrix, Ordered1, Matrix1).
explore(((_, _, C), _), coord(I, J, K), Factorization, degree(D), Ordered, Matrix, Ordered1, Matrix1) :-
  K_ is K + 1,
  arg(K_, C, Item),
  Factorization = factorization(LA, LD, _, _, crossed),
  Factorization1 = factorization([[]|LA], [[Item]|LD], 0, 1, straight),
  D1 is D + 1,
  add_factorization(coord(I, J, K_), Factorization1, degree(D1), Ordered, Matrix, Ordered1, Matrix1).
explore(((_, _, C), _), coord(I, J, K), Factorization, degree(D), Ordered, Matrix, Ordered1, Matrix1) :-
  K_ is K + 1,
  arg(K_, C, Item),
  Factorization = factorization(LA, [FD|LD], SA, SD, straight),
  SD_ is SD + 1,
  Factorization1 = factorization(LA, [[Item|FD]|LD], SA, SD_, straight),
  add_factorization(coord(I, J, K_), Factorization1, degree(D), Ordered, Matrix, Ordered1, Matrix1).
explore(((A, _, C), _), coord(I, J, K), Factorization, degree(D), Ordered, Matrix, Ordered1, Matrix1) :-
  I_ is I + 1,
  K_ is K + 1,
  arg(I_, A, Item),
  arg(K_, C, Item),
  Factorization = factorization(LA, LD, _, _, straight),
  Factorization1 = factorization([[Item]|LA], [[]|LD], 1, 0, crossed),
  D1 is D + 1,
  add_factorization(coord(I_, J, K_), Factorization1, degree(D1), Ordered, Matrix, Ordered1, Matrix1).
explore(((A, _, C), _), coord(I, J, K), Factorization, degree(D), Ordered, Matrix, Ordered1, Matrix1) :-
  I_ is I + 1,
  K_ is K + 1,
  arg(I_, A, Item),
  arg(K_, C, Item),
  Factorization = factorization([FA|LA], LD, SA, SD, crossed),
  SA_ is SA + 1,
  Factorization1 = factorization([[Item|FA]|LA], LD, SA_, SD, crossed),
  add_factorization(coord(I_, J, K_), Factorization1, degree(D), Ordered, Matrix, Ordered1, Matrix1).
explore(((_, B, _), _), coord(I, J, K), Factorization, degree(D), Ordered, Matrix, Ordered1, Matrix1) :-
  J_ is J + 1,
  arg(J_, B, Item),
  Factorization = factorization(LA, LD, _, _, straight),
  Factorization1 = factorization([[]|LA], [[Item]|LD], 0, 1, crossed),
  D1 is D + 1,
  add_factorization(coord(I, J_, K), Factorization1, degree(D1), Ordered, Matrix, Ordered1, Matrix1).
explore(((_, B, _), _), coord(I, J, K), Factorization, degree(D), Ordered, Matrix, Ordered1, Matrix1) :-
  J_ is J + 1,
  arg(J_, B, Item),
  Factorization = factorization(LA, [FD|LD], SA, SD, crossed),
  SD_ is SD + 1,
  Factorization1 = factorization(LA, [[Item|FD]|LD], SA, SD_, crossed),
  add_factorization(coord(I, J_, K), Factorization1, degree(D), Ordered, Matrix, Ordered1, Matrix1).

explore(((A, B, _), _), coord(I, J, K), Factorization, size(S), Ordered, Matrix, Ordered1, Matrix1) :-
  I_ is I + 1,
  J_ is J + 1,
  arg(I_, A, Item),
  arg(J_, B, Item),
  Factorization = factorization(LA, LD, _, _, crossed),
  Factorization1 = factorization([[Item]|LA], [[]|LD], 1, 0, straight),
  S1 is S + 1,
  add_factorization(coord(I_, J_, K), Factorization1, size(S1), Ordered, Matrix, Ordered1, Matrix1).
explore(((A, B, _), _), coord(I, J, K), Factorization, size(S), Ordered, Matrix, Ordered1, Matrix1) :-
  I_ is I + 1,
  J_ is J + 1,
  arg(I_, A, Item),
  arg(J_, B, Item),
  Factorization = factorization([FA|LA], LD, SA, SD, straight),
  SA_ is SA + 1,
  Factorization1 = factorization([[Item|FA]|LA], LD, SA_, SD, straight),
  (SA < SD -> S1 is S ; S1 is S + 1),
  add_factorization(coord(I_, J_, K), Factorization1, size(S1), Ordered, Matrix, Ordered1, Matrix1).
explore(((_, _, C), _), coord(I, J, K), Factorization, size(S), Ordered, Matrix, Ordered1, Matrix1) :-
  K_ is K + 1,
  arg(K_, C, Item),
  Factorization = factorization(LA, LD, _, _, crossed),
  Factorization1 = factorization([[]|LA], [[Item]|LD], 0, 1, straight),
  S1 is S + 1,
  add_factorization(coord(I, J, K_), Factorization1, size(S1), Ordered, Matrix, Ordered1, Matrix1).
explore(((_, _, C), _), coord(I, J, K), Factorization, size(S), Ordered, Matrix, Ordered1, Matrix1) :-
  K_ is K + 1,
  arg(K_, C, Item),
  Factorization = factorization(LA, [FD|LD], SA, SD, straight),
  SD_ is SD + 1,
  Factorization1 = factorization(LA, [[Item|FD]|LD], SA, SD_, straight),
  (SA < SD -> S1 is S ; S1 is S + 1),
  add_factorization(coord(I, J, K_), Factorization1, size(S1), Ordered, Matrix, Ordered1, Matrix1).
explore(((A, _, C), _), coord(I, J, K), Factorization, size(S), Ordered, Matrix, Ordered1, Matrix1) :-
  I_ is I + 1,
  K_ is K + 1,
  arg(I_, A, Item),
  arg(K_, C, Item),
  Factorization = factorization(LA, LD, _, _, straight),
  Factorization1 = factorization([[Item]|LA], [[]|LD], 1, 0, crossed),
  S1 is S + 1,
  add_factorization(coord(I_, J, K_), Factorization1, size(S1), Ordered, Matrix, Ordered1, Matrix1).
explore(((A, _, C), _), coord(I, J, K), Factorization, size(S), Ordered, Matrix, Ordered1, Matrix1) :-
  I_ is I + 1,
  K_ is K + 1,
  arg(I_, A, Item),
  arg(K_, C, Item),
  Factorization = factorization([FA|LA], LD, SA, SD, crossed),
  SA_ is SA + 1,
  Factorization1 = factorization([[Item|FA]|LA], LD, SA_, SD, crossed),
  (SA < SD -> S1 is S ; S1 is S + 1),
  add_factorization(coord(I_, J, K_), Factorization1, size(S1), Ordered, Matrix, Ordered1, Matrix1).
explore(((_, B, _), _), coord(I, J, K), Factorization, size(S), Ordered, Matrix, Ordered1, Matrix1) :-
  J_ is J + 1,
  arg(J_, B, Item),
  Factorization = factorization(LA, LD, _, _, straight),
  Factorization1 = factorization([[]|LA], [[Item]|LD], 0, 1, crossed),
  S1 is S + 1,
  add_factorization(coord(I, J_, K), Factorization1, size(S1), Ordered, Matrix, Ordered1, Matrix1).
explore(((_, B, _), _), coord(I, J, K), Factorization, size(S), Ordered, Matrix, Ordered1, Matrix1) :-
  J_ is J + 1,
  arg(J_, B, Item),
  Factorization = factorization(LA, [FD|LD], SA, SD, crossed),
  SD_ is SD + 1,
  Factorization1 = factorization(LA, [[Item|FD]|LD], SA, SD_, crossed),
  (SA < SD -> S1 is S ; S1 is S + 1),
  add_factorization(coord(I, J_, K), Factorization1, size(S1), Ordered, Matrix, Ordered1, Matrix1).

add_factorization(Coord, Factorization, Metric, Ordered, Matrix, Ordered, Matrix1) :-
  get_assoc(Coord, Matrix, solution(Metric, Factorizations)),
  !,
  put_assoc(Coord, Matrix, solution(Metric, [Factorization|Factorizations]), Matrix1).
add_factorization(Coord, Factorization, Metric, Ordered, Matrix, Ordered1, Matrix1) :-
  get_assoc(Coord, Matrix, solution(PrevMetric, _)),
  !,
  compound_name_arguments(Metric, MetricName, [N]),
  compound_name_arguments(PrevMetric, MetricName, [PrevN]),
  (PrevN < N ->
    Ordered1 = Ordered,
    Matrix1 = Matrix
    ;
    put_assoc(Coord, Matrix, solution(Metric, [Factorization]), Matrix1),
    get_assoc(PrevMetric, Ordered, PrevCoordList),
    subtract(PrevCoordList, [Coord], PrevCoordList1),
    put_assoc(PrevMetric, Ordered, PrevCoordList1, Ordered_),
    get_assoc_default(Metric, Ordered_, CoordList, []),
    put_assoc(Metric, Ordered_, [Coord|CoordList], Ordered1)
  ).
add_factorization(Coord, Factorization, Metric, Ordered, Matrix, Ordered1, Matrix1) :-
  put_assoc(Coord, Matrix, solution(Metric, [Factorization]), Matrix1),
  get_assoc_default(Metric, Ordered, CoordList, []),
  put_assoc(Metric, Ordered, [Coord|CoordList], Ordered1).

format_factorization(ReverseFactorization, Factorization, Output) :-
  format_factorization(ReverseFactorization, factorization([],[]), Factorization, [], Output).
format_factorization(factorization([], [], _, _, _), Factorization, Factorization, Output, Output).
format_factorization(factorization([FA|LA], [FD|LD], _, _, _), factorization(LAAcc, LDAcc), Factorization, OutputAcc, Output) :-
  reverse(FA, AF),
  reverse(FD, DF),
  append(DF, OutputAcc, OutputAcc1),
  format_factorization(factorization(LA, LD, _, _, _), factorization([AF|LAAcc], [DF|LDAcc]), Factorization, OutputAcc1, Output).
