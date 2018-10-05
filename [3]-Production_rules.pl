% SICStus PROLOG: Declaracoes iniciais
:- set_prolog_flag( discontiguous_warnings,off ).
:- set_prolog_flag( single_var_warnings,off ).
:- set_prolog_flag( unknown,fail ).
%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% SICStus PROLOG: definicoes iniciais
:- op( 800,fx,se ).
:- op( 800,fx,facto ).
:- op( 700,xfx,entao ).
:- op( 300,xfy,ou ).
:- op( 200,xfy,e ). 
:- op( 900,xfx,é ).
:- op( 900,xfx,::). 
:- op( 900,xfy,::: ). 
:- op( 400,xfy,porque). 
:- op( 400,xfy,era). 
:- op( 400,xfy,com).
:- dynamic grau/1.
:- dynamic '::'/2.
:- dynamic ':::'/2.
:- dynamic facto/1.

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Base de Conhecimento 

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado sintoma: sintoma -> { V,F } 

sintoma('Fadiga').
sintoma('Vómitos').
sintoma('Nauseas').
sintoma('Hiporexia').
sintoma('Insónia').
sintoma('Hipertensão').
sintoma('Edema').
sintoma('Oligúria').
sintoma('Tonturas').
sintoma('Perda de memória').
sintoma('Agnosia').
sintoma('Depressão').
sintoma('Stress').

%Extensão do predicado facto: termo -> {V,F}
facto(P) :-
	findall((X,Gt), (facto X :: Gt), P).

%facto ('Vómitos') :: 'Provavel'.

% Extensao do predicado grau: grau -> { V,F }

grau('Impossivel').
grau('Pouco provavel').
grau('Provavel').
grau('Muito provavel').
grau('Certo').

%--------------------------------- - - - - - - - - - -  -  -  -  -   -

% Construcao de Regras de Producao: se CONDICAO entao CONCLUSAO :: Ocorrencia com Tratamento

(se 'Nauseas' ou 'Vómitos' ou 'Fadiga' ou 'Hiporexia' entao 'Nefrite') :: ('Provavel' com 'Repouso durante 5 dias' ) . 
(se 'Nefrite' e 'Insónia' e 'Hipertensão' entao 'Glomerulonefrite')  :: ('Certo' com 'Repouso durante 10 dias' ) .
(se 'Glomerulonefrite' e 'Edema' e 'Oligúria' entao 'Sindrome nefritica'):: ('Certo' com 'Benuron 1000 durante 3 dias' ) .
(se 'Tonturas' e 'Fadiga' entao 'Anemia')::('Muito provavel' com  'Ferronil durante 1 semana').
(se 'Agnosia' e 'Perda de memória' e 'Depressão' e 'Stress' entao 'Alzheimer') :: ('Certo' com 'Memantina durante 3 meses').
%--------------------------------- - - - - - - - - - -  -  -  -  -   -

% Extensão do predicado adiciona: sintoma,grau ->{V,F}.
adiciona(S,G):- 
	solucoes( Invariante,+( facto( S ) :: G ):::Invariante,Lista ),
	sintoma(S),
	grau(G),
	insercao(S,G),
	teste(Lista). 

% Extensão do predicado troca: sintoma,grau ->{V,F}.
troca(S,G) :-
	(facto(S) :: _),
	remocao(S),
	adiciona(S,G).

% Extensão do predicado remocao: sintoma ->{V,F}.
remocao(S) :- 
	retract(facto(S)::G).

% Extensão do predicado clear ->{V,F}.
clear :- retractall(facto(S)::G).

% Invariante que impede a insercao de Sintomas repetidos
+(facto T :: G1) ::: (solucoes(_,(facto T :: G2),S),comprimento(S,N), N==1).

% Invariante que limita o grau. nao é necessario no caso do adicionaram.
%+( facto D :: G ) ::: (solucoes(_,((facto T :: G2),G2\='Certo',G2\='Muito provavel',G2\='Provavel',G2\='Pouco provavel',G2\='Impossivel'),S),comprimento(S,N), N==0).

% Invariante que impede a insercao de tratamentos repetidos
%+(Tratamento X) ::: (solucoes(X,(Tratamento X),S),comprimento(S,N), N==1).

% Extensão do predicado diagnostico: doença, explicacao, ocorrencia, prescriçao ->{V,F}.
diagnostico( CS, (CS é Gt) porque Ec, Gt, [T]) :-
    (se CC entao CS) :: (G com T),
    demo( CC, Ec ,G2, T2 ),
    comb(G,G2,Gt),
    Gt\='Impossivel'.
	
    % pertence(Gt, ['Certo', 'Muito provavel', 'Provavel', 'Pouco provavel']).

demo( CC, CC era G, G, [] ) :-
    nonvar(CC),
    facto CC :: G.
 
demo( Q1 e Q2,E1 e E2, G, T ) :-
    nonvar(Q1), nonvar(Q2),
    demo( Q1,E1, G1, T1 ),
    demo( Q2,E2, G2, T2 ),
    concatenar(T1,T2,T),
    conde(G1,G2,G).
  
demo(Q1 ou Q2, E1, G1, T1 ) :-
    nonvar(Q1), nonvar(Q2),
    demo(Q1,E1,G1,T1),
    nao(demo(Q2,E2,G2,T2)).

demo(Q1 ou Q2, E2, G2, T2 ) :-
    nonvar(Q1), nonvar(Q2),
    nao(demo(Q1,E1,G1,T1)),
    demo(Q2,E2,G2,T2).

demo(Q1 ou Q2, E1 ou E2, G, T ) :-
    nonvar(Q1), nonvar(Q2),
    demo(Q1,E1,G1,T1),
    demo(Q2,E2,G2,T2),
    concatenar(T1,T2,T),
    condou(G1,G2,G).
  
demo( CC, C, G, T ) :-
   nonvar(CC),
   diagnostico( CC, C, G, T ).

% Extensão do predicado conde: G1,G2,G->{V,F}.
conde('Impossivel','Impossivel','Impossivel').
conde('Impossivel','Pouco provavel','Impossivel').
conde('Impossivel','Provavel','Impossivel').
conde('Impossivel','Muito provavel','Impossivel').
conde('Impossivel','Certo','Impossivel').
conde('Pouco provavel','Impossivel','Impossivel').
conde('Pouco provavel','Pouco provavel','Pouco provavel').
conde('Pouco provavel','Provavel','Pouco provavel').
conde('Pouco provavel','Muito provavel','Pouco provavel').
conde('Pouco provavel','Certo','Pouco provavel').
conde('Provavel','Impossivel','Impossivel').
conde('Provavel','Pouco provavel','Pouco provavel').
conde('Provavel','Provavel','Provavel').
conde('Provavel','Muito provavel','Provavel').
conde('Provavel','Certo','Provavel').
conde('Muito provavel','Impossivel','Impossivel').
conde('Muito provavel','Pouco provavel','Pouco provavel').
conde('Muito provavel','Provavel','Provavel').
conde('Muito provavel','Muito provavel','Muito provavel').
conde('Muito provavel','Certo','Muito provavel').
conde('Certo','Impossivel','Impossivel').
conde('Certo','Pouco provavel','Pouco provavel').
conde('Certo','Provavel','Provavel').
conde('Certo','Muito provavel','Muito provavel').
conde('Certo','Certo','Certo').

% Extensão do predicado condou: G1,G2,G->{V,F}.
condou('Impossivel','Impossivel','Impossivel').
condou('Impossivel','Pouco provavel','Pouco provavel').
condou('Impossivel','Provavel','Provavel').
condou('Impossivel','Muito provavel','Muito provavel').
condou('Impossivel','Certo','Certo').
condou('Pouco provavel','Impossivel','Pouco provavel').
condou('Pouco provavel','Pouco provavel','Pouco provavel').
condou('Pouco provavel','Provavel','Provavel').
condou('Pouco provavel','Muito provavel','Muito provavel').
condou('Pouco provavel','Certo','Certo').
condou('Provavel','Impossivel','Provavel').
condou('Provavel','Pouco provavel','Provavel').
condou('Provavel','Provavel','Provavel').
condou('Provavel','Muito provavel','Muito provavel').
condou('Provavel','Certo','Certo').
condou('Muito provavel','Impossivel','Muito provavel').
condou('Muito provavel','Pouco provavel','Muito provavel').
condou('Muito provavel','Provavel','Muito provavel').
condou('Muito provavel','Muito provavel','Muito provavel').
condou('Muito provavel','Certo','Muito provavel').
condou('Certo','Impossivel','Certo').
condou('Certo','Pouco provavel','Certo').
condou('Certo','Provavel','Certo').
condou('Certo','Muito provavel','Certo').
condou('Certo','Certo','Certo').

% Extensão do predicado comb: G1,G2,G->{V,F}.
comb('Impossivel','Impossivel','Impossivel').
comb('Impossivel','Pouco provavel','Impossivel').
comb('Impossivel','Provavel','Pouco provavel').
comb('Impossivel','Muito provavel','Pouco provavel').
comb('Impossivel','Certo','Provavel').
comb('Pouco provavel','Impossivel','Impossivel').
comb('Pouco provavel','Pouco provavel','Pouco provavel').
comb('Pouco provavel','Provavel','Pouco provavel').
comb('Pouco provavel','Muito provavel','Provavel').
comb('Pouco provavel','Certo','Provavel').
comb('Provavel','Impossivel','Pouco provavel').
comb('Provavel','Pouco provavel','Pouco provavel').
comb('Provavel','Provavel','Provavel').
comb('Provavel','Muito provavel','Provavel').
comb('Provavel','Certo','Muito provavel'). 
comb('Muito provavel','Impossivel','Pouco provavel').
comb('Muito provavel','Pouco provavel','Provavel').
comb('Muito provavel','Provavel','Provavel').
comb('Muito provavel','Muito provavel','Muito provavel').
comb('Muito provavel','Certo','Muito provavel').
comb('Certo','Impossivel','Provavel').
comb('Certo','Pouco provavel','Provavel').
comb('Certo','Provavel','Muito provavel').
comb('Certo','Muito provavel','Muito provavel').
comb('Certo','Certo','Certo').

% Extensao do predicado soluçoes: Arquetipo,Condicao,Soluçao-> {V,F}
solucoes(X,Y,Z):-
	findall(X,Y,Z).

% Extensao do predicado pertence: X, L-> {V,F}
pertence( X,[X|L] ).
pertence( X,[Y|L] ) :-
    X \== Y,              
    pertence( X,L ).

%Extensão do predicado insercao: facto Termo :: G -> {V,F}.
insercao(Termo,Grau):-
    assert( facto Termo :: Grau ).
insercao(Termo,Grau ):-
    retract( facto Termo :: Grau ),!,fail.

%Extensao do predicado teste: lista -> {V,F}
teste( [] ).
teste( [R|LR] ) :-
	R, teste( LR ).
 
% Extensao do predicado comprimento: Lista,Comprimento -> {V,F}
comprimento( [],0 ).
comprimento( [X|L],N ) :-
    comprimento( L,N1 ),
    N is N1+1.

% Extensao do predicado concatenar: Lista1,Lista2,Resultado -> {V,F}
concatenar([],X,X).
concatenar([X|Y],Z,[X|R]):-
    concatenar(Y,Z,R).

% Extensao do meta-predicado nao: QUESTAO -> { V,F }
nao( QUESTAO ) :-
    QUESTAO, !, fail.
nao( QUESTAO ).