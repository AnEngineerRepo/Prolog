%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% PROGRAMAÇÃO EM LOGICA, CONHECIMENTO E RACIOCINIO - TRABALHO PRÁTICO 2

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% SICStus PROLOG: Declaracoes iniciais

:- set_prolog_flag( discontiguous_warnings,off ).
:- set_prolog_flag( single_var_warnings,off ).
:- set_prolog_flag( unknown,fail ).

% SICStus PROLOG: definicoes iniciais

:- op( 300,xfy,ou ).
:- op( 200,xfy,e ).
:- op( 900,xfy,'::' ).
:- dynamic prestador/4.
:- dynamic utente/4.
:- dynamic consulta/5.
:- dynamic '-'/1.
:- dynamic excecao/1.
:- dynamic desconhecido/1.

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Base de conhecimento

% Extensão do predicado utente: idUt,nome,idade,morada -->{V,F,D}.
utente(01,ana,26,'Braga').
utente(02,bernardo,35,'Guimarães').
utente(03,rui,70,'Vizela').
utente(04,vera,20,'Braga').
utente(05,andre,69,'Esposende').
utente(06,filipa,42,'Braga').

% Extensão do predicado prestador: idPrest,nome,funcao,servico -->{V,F,D}.
prestador(01,maria,medico,ortopedia).
prestador(02,jose,medico,cardiologia).
prestador(03,sara,medico,cardiologia).
prestador(04,alcides,medico,urologia).
prestador(05,catarina,enfermeiro,cardiologia).
prestador(06,rita,medico,ortopedia).
-prestador(07,abilio,enfermeiro,urologia).

% Extensão do predicado consulta: data,idUt,idPrest,descricao,custo -->{V,F,D}.
consulta(20160412,03,04,'analises clinicas',30).
consulta(20160821,01,02,'auscultacao',10).
consulta(20160911,06,06,'rotina',30).

%Pressuposto do mundo fechado
-utente(IDU,NU,I,M):-  nao(excecao(utente(IDU,NU,I,M))), nao(utente(IDU,NU,I,M)).
-prestador(IDP,NP,F,SE):- nao(prestador(IDP,NP,F,SE)), nao(excecao(prestador(IDP,NP,F,SE))).
-consulta(DD,IDU,IDP,D,C):- nao(consulta(DD,IDU,IDP,D,C)), nao(excecao(consulta(DD,IDU,IDP,D,C))).

%Conhecimento imperfeito do tipo incerto
prestador(08,vanessa,medico,desconhecido).
excecao(prestador(IDP,NP,F,SE)):- prestador(IDP,NP,F,desconhecido).

%Conhecimento imperfeito do tipo impreciso (2 exemplos)
excecao(consulta(20160706,05,04,'analises clinicas',C)):- C>=10,C=<20.

excecao(utente(07,ricardo,30,'Braga')).
excecao(utente(07,ricardo,30,'Fafe')).

%Conhecimento imperfeito do tipo interdito
utente(08,daniela,proib,'Braga').
excecao(utente(IDU,NU,I,M)):- utente(IDU,NU,proib,M).
interdito(proib).
+utente(IDU,NU,I,M)::(findall( I,(utente(08,daniela,I,'Braga'), nao(interdito(I))),S), comprimento(S,N), N==0).

%Invariantes estruturais
%impede a colocação de conhecimento repetido para utente e prestador
+utente(IDU,NU,I,M)::(findall((IDU,NU,I,M),(utente(IDU,NU,I,M)),S),comprimento(S,N),N==1). 
+prestador(IDP,NP,F,SE)::(findall((IDP,NP,F,SE),(prestador(IDP,NP,F,SE)),S),comprimento(S,N),N==1).
+consulta(DD,IDU,IDP,D,C)::(findall((DD,IDU,IDP,D,C),(consulta(DD,IDU,IDP,D,C)),S),comprimento(S,N),N==1).

%remoção de conhecimento
-prestador(IDP,NP,F,SE)::(findall((DD,IDU,D,C), consulta(DD,IDU,IDP,D,C),S), comprimento(S,N),N==0). 
-utente(IDU,NU,I,M)::(findall((DD,IDP,D,C), consulta(DD,IDU,IDP,D,C),S), comprimento(S,N),N==0). 

%Invariantes referenciais
%só insiro a consulta se o prestador e o utente existirem 
+consulta(DD,IDU,IDP,D,C)::(utente(IDU,E,F,G), prestador(IDP,X,Y,Z)). 

%nao se pode inserir utentes ou prestadores com o mesmo id
+utente(IDU,NU,I,M)::(findall(IDU,(utente(IDU,A,B,C)),S), comprimento(S,N),N==1). 
+prestador(IDP,NP,F,SE)::(findall(IDP,(prestador(IDP,A,B,C)),S), comprimento(S,N),N==1). 

%é proibido cobrar qualquer consulta um preço superior a 100 euros
+consulta( DD,IDU,IDP,D,C ) :: (findall( C,(consulta(X,Y,Z,W,C ) , C>100),S), comprimento( S,N ), N == 0).

%instituiçao nao tem licença para tratar de menores
+utente(IDU,NU,I,M)::(utente(X,Y,I,Z), I>18).

% invariante da nova evolução
%+prestador(IDP,NP,F,SE)::(findall(_,(-prestador(IDP,NP,F,SE)),S), comprimento(S,N),N==0).
%--------------------------------- - - - - - - - - - -  -  -  -  -   -

% Extensão do meta-predicado demoe: Questões,Resposta -> {V,F,D}.
% Extensão do meta-predicado demoou: Questões,Resposta -> {V,F,D}.
demoe(Q,R):-conde(Q,R).
demoou(Q,R):-condou(Q,R).

% Extensão do predicado conde: Questões,Resposta -> {V,F,D}.
conde( [],verdadeiro ). 
conde( [Q1|Q2],verdadeiro ):- Q1, conde( Q2,verdadeiro ).
conde( [Q1|Q2],falso ):- (-Q1).
conde( [Q1|Q2],falso ):- nao(-Q1), conde(Q2,falso).
conde( [Q1|Q2],desconhecido ):-  nao(Q1), nao(-Q1), conde(Q2,R), R\=falso.
conde( [Q1|Q2],desconhecido ):- Q1, conde( Q2,desconhecido ).

% Extensão do predicado condou: Questões,Resposta -> {V,F,D}.
condou( [],falso ).
condou( [Q1|Q2],verdadeiro ):- Q1.
condou( [Q1|Q2],verdadeiro ):- nao(Q1), condou(Q2,verdadeiro).
condou( [Q1|Q2],desconhecido ):- nao(Q1),condou( Q2,desconhecido ).
condou( [Q1|Q2],desconhecido ):- nao(Q1), nao(-Q1), condou(Q2,R), R\=verdadeiro.
condou( [Q1|Q2],falso ):- (-Q1), condou(Q2,falso). 

%Demo alternativo.
% Extensão do meta-predicado demo: Questões,Resposta -> {V,F,D}.
demo( Q1 e Q2,verdadeiro ):- Q1, demo( Q2,verdadeiro ).
demo( Q1 e Q2,falso ):- (-Q1).
demo( Q1 e Q2,falso ):- demo(Q2,falso).
demo( Q1 e Q2,desconhecido ):-  nao(Q1), nao(-Q1), demo(Q2,R), R\=falso.
demo( Q1 e Q2,desconhecido ):- Q1, demo( Q2,desconhecido ).

demo( Q1 ou Q2,verdadeiro ):- Q1.
demo( Q1 ou Q2,verdadeiro ):- demo(Q2,verdadeiro).
demo( Q1 ou Q2,desconhecido ):- nao(Q1),demo( Q2,desconhecido ).
demo( Q1 ou Q2,desconhecido ):- nao(Q1), nao(-Q1), demo(Q2,R), R\=verdadeiro.
demo( Q1 ou Q2,falso ):- (-Q1), demo(Q2,falso).

% Extensao do meta-predicado demo: Questao,Resposta -> {V,F,D}.
demo( Q,verdadeiro ) :-
Q.
demo( Q,falso ) :-
-Q.
demo( Q,desconhecido ) :-
nao(Q), nao(-Q), Q\=Q1 e Q2, Q\=Q1 ou Q2. 

% Extensao do meta-predicado nao: Questao -> {V,F}
nao(Q):- Q,!,fail.
nao(Q).

%Evolucao de conhecimento

% Extensão do predicado adicionarpos: Termo -> {V,F}.
adicionarpos(Termo):-
     remover(-Termo),
     adicionar(Termo).
adicionarpos(Termo):-
	adicionar(Termo).

% Extensão do predicado adicionarneg: Termo -> {V,F}.
adicionarneg(Termo):-
     remover(Termo),
     adicionar(-Termo).
adicionarneg(Termo):-
	adicionar(-Termo).

% Extensão do predicado adicionardescpos: Termo -> {V,F}.
adicionardescpos(Termo):-
	demoe([Termo],falso),
	adicionar(Termo).

% Extensão do predicado adicionardescneg: Termo -> {V,F}.
adicionardescneg(Termo):-
	demoe([Termo],falso),
	adicionar(-Termo).

% Extensão do predicado adicionardescoutro: Termo novo, Termo antigo-> {V,F}.
adicionardescoutro( Termo_novo,Termo_a_retirar ):-
	remover( Termo_a_retirar ),
	adicionar( Termo_novo ).

% Extensão do predicado adicionarimprpos: Termo -> {V,F}.
adicionarimprpos(Termo,Termo_esclarecido):-
     remover(excecao(Termo)),
     remover(excecao(Termo_esclarecido)),
     adicionar(Termo).

% Extensão do predicado adicionarimprneg: Termo -> {V,F}.
adicionarimprneg(Termo,Termo_esclarecido):-
     remover(excecao(Termo)),
     remover(excecao(Termo_esclarecido)),
     adicionar(-Termo).


%Melhoria evoluçao:registo de conhecimento desconhecido
% Extensão do predicado registardescimp: Termo -> {V,F}.
registardescimp( Termo_conhecido, Termo_duvidoso):-
	remover( Termo_conhecido ),
	adicionar( excecao( Termo_conhecido ) ),
	adicionar( excecao( Termo_duvidoso ) ).
	
% Extensão do predicado registarincerto: Termo -> {V,F}.
%registarincerto(Termo) :- 
	%adicionar(Termo), 
	%Termo=..[X|LT],
	%alteracao(LT,LN),
	%LNN=..[prestador|LN],
	%adicionar((excecao(prestador(IDP,NP,F,SE)) :- LNN)).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
%Predicados evolucao auxiliares
%Extensão do predicado adicionar: termo -> {V,F}
adicionar( Termo ) :-
findall( Invariante,+(Termo)::Invariante,Lista ),
insercao( Termo ),
teste( Lista ).

%Extensão do predicado insercao: termo -> {V,F}
insercao( Termo ) :-
assert( Termo ).
insercao( Termo ) :-
retract(Termo ),!,fail.

%Extensão do predicado remover: termo -> {V,F}
remover( Termo ) :-
findall( Invariante,-(Termo)::Invariante,Lista ),
teste( Lista ),
retract( Termo ).

%Extensão do predicado teste: Lista -> {V,F}
teste( [ ] ).
teste( [R|L] ) :-
R, teste(L).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
%Predicados auxiliares
%Extensao do predicado comprimento: lista, comprimento -> {V,F}
comprimento( [],0 ).
comprimento( [X|L],N ) :-
comprimento( L,N1 ),
N is N1+1.

% Extensao do meta-predicado nao: Questao -> {V,F}
nao(Q):- Q,!,fail.
nao(Q).


