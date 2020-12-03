:- use_module(library(clpfd)).

sequence_analogy(A, B, C, Results) :-
    sequence_analogy(A, B, C, Results, _, _, _).

sequence_analogy(A, B, C, Results, DegreeCap, SizeCap, CapReached) :-
    length(A, LA),
    length(B, LB),
    length(C, LC),
    sequence_analogy(A, B, C, [[], 1, 0, [0, 0, 0, 0], [LA, LB, LC], [[[]], [[]], [[]], [[]]]], Results, DegreeCap, SizeCap, CapReached).

sequence_analogy([], [], [], Acc, [Result], DegreeCap, SizeCap, false) :-
    Acc = [D, Degree, Size, SList, [0, 0, 0], Factorization],
    max_list(SList, LastSize),
    S is Size + LastSize,
    Degree #=< DegreeCap,
    S #=< SizeCap,
    reorder_res([D, Degree, S, Factorization], Result),
%    format_res([D, Degree, S, Factorization], ResultFormatted),
%    format('Succeeded:~n~s~n~n', [ResultFormatted]),
    !.
sequence_analogy(A, B, C, Acc, Results, DegreeCap, SizeCap, CapReached) :-
    Acc = [_, Degree, Size, SList, LengthsAhead, _],
    max_list(SList, LastSize),
    max_list(LengthsAhead, MinSizeAhead),
    Degree #=< DegreeCap,
    Size + LastSize + MinSizeAhead #=< SizeCap,
    sequence_analogy(ab, A, B, C, Acc, Res1, DegreeCap, SizeCap, CapReached1),
    sequence_analogy(cd, A, B, C, Acc, Res2, DegreeCap, SizeCap, CapReached2),
    sequence_analogy(ac, A, B, C, Acc, Res3, DegreeCap, SizeCap, CapReached3),
    sequence_analogy(bd, A, B, C, Acc, Res4, DegreeCap, SizeCap, CapReached4),
    is_true(CapReached1; CapReached2; CapReached3; CapReached4, CapReached),
    foldl(union, [Res1, Res2, Res3, Res4], [], Results),
    !.
sequence_analogy(_, _, _, _, [], _, _, true).

is_true(X, true) :- X, !.
is_true(_, false).

sequence_analogy(ab, [E|A], [E|B], C, Acc, Results, DegreeCap, SizeCap, CapReached) :-
    Acc = [D, Degree, Size, [SA, SB, SC, SD], LengthsAhead, [[HF1|TFA], [HF1|TFB], [HF2|TFC], [HF2|TFD]]],
    LengthsAhead = [LA, LB, LC],
    NextLA is LA - 1,
    NextLB is LB - 1,
    NextLengthsAhead = [NextLA, NextLB, LC],
    NextSA is SA + 1,
    NextSB is SB + 1,
    NextAcc = [D, Degree, Size, [NextSA, NextSB, SC, SD], NextLengthsAhead, [[[E|HF1]|TFA], [[E|HF1]|TFB], [HF2|TFC], [HF2|TFD]]],
    sequence_analogy(A, B, C, NextAcc, Results, DegreeCap, SizeCap, CapReached),
    !.
sequence_analogy(ab, [E|A], [E|B], C, Acc, Results, DegreeCap, SizeCap, CapReached) :-
    Acc = [D, Degree, Size, SList, LengthsAhead, [FA, FB, FC, FD]],
    [FA, FB, FC, FD] = [[HF1|_], [HF2|_], [HF1|_], [HF2|_]],
    LengthsAhead = [LA, LB, LC],
    NextLA is LA - 1,
    NextLB is LB - 1,
    NextLengthsAhead = [NextLA, NextLB, LC],
    max_list(SList, LastSize),
    NextSize is Size + LastSize,
    NextDegree is Degree + 1,
    NextAcc = [D, NextDegree, NextSize, [1, 1, 0, 0], NextLengthsAhead, [[[E]|FA], [[E]|FB], [[]|FC], [[]|FD]]],
    sequence_analogy(A, B, C, NextAcc, Results, DegreeCap, SizeCap, CapReached),
    !.
sequence_analogy(cd, A, B, [E|C], Acc, Results, DegreeCap, SizeCap, CapReached) :-
    Acc = [D, Degree, Size, [SA, SB, SC, SD], LengthsAhead, [[HF1|TFA], [HF1|TFB], [HF2|TFC], [HF2|TFD]]],
    LengthsAhead = [LA, LB, LC],
    NextLC is LC - 1,
    NextLengthsAhead = [LA, LB, NextLC],
    NextSC is SC + 1,
    NextSD is SD + 1,
    NextAcc = [[E|D], Degree, Size, [SA, SB, NextSC, NextSD], NextLengthsAhead, [[HF1|TFA], [HF1|TFB], [[E|HF2]|TFC], [[E|HF2]|TFD]]],
    sequence_analogy(A, B, C, NextAcc, Results, DegreeCap, SizeCap, CapReached),
    !.
sequence_analogy(cd, A, B, [E|C], Acc, Results, DegreeCap, SizeCap, CapReached) :-
    Acc = [D, Degree, Size, SList, LengthsAhead, [FA, FB, FC, FD]],
    [FA, FB, FC, FD] = [[HF1|_], [HF2|_], [HF1|_], [HF2|_]],
    LengthsAhead = [LA, LB, LC],
    NextLC is LC - 1,
    NextLengthsAhead = [LA, LB, NextLC],
    max_list(SList, LastSize),
    NextSize is Size + LastSize,
    NextDegree is Degree + 1,
    NextAcc = [[E|D], NextDegree, NextSize, [0, 0, 1, 1], NextLengthsAhead, [[[]|FA], [[]|FB], [[E]|FC], [[E]|FD]]],
    sequence_analogy(A, B, C, NextAcc, Results, DegreeCap, SizeCap, CapReached),
    !.
sequence_analogy(ac, [E|A], B, [E|C], Acc, Results, DegreeCap, SizeCap, CapReached) :-
    Acc = [D, Degree, Size, [SA, SB, SC, SD], LengthsAhead, [[HF1|TFA], [HF2|TFB], [HF1|TFC], [HF2|TFD]]],
    LengthsAhead = [LA, LB, LC],
    NextLA is LA - 1,
    NextLC is LC - 1,
    NextLengthsAhead = [NextLA, LB, NextLC],
    NextSA is SA + 1,
    NextSC is SC + 1,
    NextAcc = [D, Degree, Size, [NextSA, SB, NextSC, SD], NextLengthsAhead, [[[E|HF1]|TFA], [HF2|TFB], [[E|HF1]|TFC], [HF2|TFD]]],
    sequence_analogy(A, B, C, NextAcc, Results, DegreeCap, SizeCap, CapReached),
    !.
sequence_analogy(ac, [E|A], B, [E|C], Acc, Results, DegreeCap, SizeCap, CapReached) :-
    Acc = [D, Degree, Size, SList, LengthsAhead, [FA, FB, FC, FD]],
    [FA, FB, FC, FD] = [[HF1|_], [HF1|_], [HF2|_], [HF2|_]],
    LengthsAhead = [LA, LB, LC],
    NextLA is LA - 1,
    NextLC is LC - 1,
    NextLengthsAhead = [NextLA, LB, NextLC],
    max_list(SList, LastSize),
    NextSize is Size + LastSize,
    NextDegree is Degree + 1,
    NextAcc = [D, NextDegree, NextSize, [1, 0, 1, 0], NextLengthsAhead, [[[E]|FA], [[]|FB], [[E]|FC], [[]|FD]]],
    sequence_analogy(A, B, C, NextAcc, Results, DegreeCap, SizeCap, CapReached),
    !.
sequence_analogy(bd, A, [E|B], C, Acc, Results, DegreeCap, SizeCap, CapReached) :-
    Acc = [D, Degree, Size, [SA, SB, SC, SD], LengthsAhead, [[HF1|TFA], [HF2|TFB], [HF1|TFC], [HF2|TFD]]],
    LengthsAhead = [LA, LB, LC],
    NextLB is LB - 1,
    NextLengthsAhead = [LA, NextLB, LC],
    NextSB is SB + 1,
    NextSD is SD + 1,
    NextAcc = [[E|D], Degree, Size, [SA, NextSB, SC, NextSD], NextLengthsAhead, [[HF1|TFA], [[E|HF2]|TFB], [HF1|TFC], [[E|HF2]|TFD]]],
    sequence_analogy(A, B, C, NextAcc, Results, DegreeCap, SizeCap, CapReached),
    !.
sequence_analogy(bd, A, [E|B], C, Acc, Results, DegreeCap, SizeCap, CapReached) :-
    Acc = [D, Degree, Size, SList, LengthsAhead, [FA, FB, FC, FD]],
    [FA, FB, FC, FD] = [[HF1|_], [HF1|_], [HF2|_], [HF2|_]],
    LengthsAhead = [LA, LB, LC],
    NextLB is LB - 1,
    NextLengthsAhead = [LA, NextLB, LC],
    max_list(SList, LastSize),
    NextSize is Size + LastSize,
    NextDegree is Degree + 1,
    NextAcc = [[E|D], NextDegree, NextSize, [0, 1, 0, 1], NextLengthsAhead, [[[]|FA], [[E]|FB], [[]|FC], [[E]|FD]]],
    sequence_analogy(A, B, C, NextAcc, Results, DegreeCap, SizeCap, CapReached),
    !.
sequence_analogy(_, _, _, _, Acc, [], _, _, false) :-
%    Acc = [D, Degree, Size, SList, LengthsAhead, Factorization],
%    max_list(SList, LastSize),
%    max_list(LengthsAhead, MinSizeAhead),
%    S is Size + LastSize + MinSizeAhead,
%    format_res([D, Degree, S, Factorization], ResultFormatted),
%    format('Failed:~n~s~n~n', [ResultFormatted]),
%    (Degree = 5, S >= 21) -> sleep(1);
    true.

format_res([_, Degree, Size, [FA, FB, FC, FD]], Formatted) :-
    format_factorization((FA, FB, FC, FD), Factorization),
    format(string(Formatted), "~sDegree: ~g~nSize: ~g~n", [Factorization, Degree, Size]).

format_factorization(Factors, String) :-
    format_factorization_(Factors, (FA, FB, FC, FD)),
    foldl(string_concat, FA, '', StrA),
    foldl(string_concat, FB, '', StrB),
    foldl(string_concat, FC, '', StrC),
    foldl(string_concat, FD, '', StrD),
    format(string(String), "~s~n~s~n~s~n~s~n", [StrA, StrB, StrC, StrD]).
format_factorization_(([], [], [], []), ([], [], [], [])).
format_factorization_(([A|FA], [B|FB], [C|FC], [D|FD]), (SA, SB, SC, SD)) :-
    maplist(length, [A, B, C, D], [LA, LB, LC, LD]),
    max_list([LA, LB, LC, LD], Max),
    append(A, CA, FinalA),
    append(B, CB, FinalB),
    append(C, CC, FinalC),
    append(D, CD, FinalD),
    length(FinalA, Max),
    length(FinalB, Max),
    length(FinalC, Max),
    length(FinalD, Max),
    repeating_list(' ', CA),
    repeating_list(' ', CB),
    repeating_list(' ', CC),
    repeating_list(' ', CD),
    append(FinalA, SSA, SA),
    append(FinalB, SSB, SB),
    append(FinalC, SSC, SC),
    append(FinalD, SSD, SD),
    format_factorization_((FA, FB, FC, FD), (SSA, SSB, SSC, SSD)).

repeating_list(_, []).
repeating_list(Symbol, [Symbol|L]) :-
    repeating_list(Symbol, L).

reorder_res([D_, Degree, Size, [FA_, FB_, FC_, FD_]], [D, Degree, Size, [FA, FB, FC, FD]]) :-
    reverse(D_, D),
    maplist(reverse, FA_, FA__),
    maplist(reverse, FB_, FB__),
    maplist(reverse, FC_, FC__),
    maplist(reverse, FD_, FD__),
    maplist(reverse, [FA__, FB__, FC__, FD__], [FA, FB, FC, FD]).
