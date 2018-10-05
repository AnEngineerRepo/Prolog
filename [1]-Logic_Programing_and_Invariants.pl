:- set_prolog_flag( discontiguous_warnings,off ).
:- set_prolog_flag( single_var_warnings,off ).
:- set_prolog_flag( unknown,fail ).

:- op( 900,xfy,'::' ).
:- dynamic instituicao/1.
:- dynamic especialidade/2.
:- dynamic servico/3.
:- dynamic medico/4.
:- dynamic utente/4.
:- dynamic consulta/8.

%  Extensão do predicado instituicao: I(Instituição) --> {V,F}.
instituicao( 'Hospital de Braga' ).
instituicao( 'Hospital Privado' ).

%  Extensão do predicado especialidade: E(especialidade),I(instituição) --> {V,F}.
especialidade( 'Cardiologia', 'Hospital de Braga' ).
especialidade( 'Ginecologia', 'Hospital de Braga' ).
especialidade( 'Psiquiatria', 'Hospital de Braga' ).
especialidade( 'Cardiologia', 'Hospital Privado' ).
especialidade( 'Psiquiatria', 'Hospital Privado' ).

%  Extensão do predicado servico: S(serviço),E(especialidade),I(instituição) --> {V,F}.
servico( 'Urgência', 'Cardiologia', 'Hospital de Braga' ).
servico( 'Urgência', 'Cardiologia', 'Hospital Privado' ).
servico( 'Consulta Externa', 'Ginecologia', 'Hospital de Braga' ).
servico( 'Análises Clínicas', 'Cardiologia', 'Hospital Privado' ).
servico( 'Análises Clínicas', 'Psiquiatria', 'Hospital Privado' ).
servico( 'Urgência', 'Psiquiatria', 'Hospital Privado' ).

%  Extensão do predicado medico: M(medico),S(serviço),E(especialidade),I(instituição) --> {V,F}.
medico( 'André', 'Urgência', 'Cardiologia', 'Hospital de Braga' ).
medico( 'Maria', 'Urgência', 'Cardiologia', 'Hospital de Braga' ).
medico( 'Cristiano', 'Consulta Externa', 'Ginecologia', 'Hospital de Braga' ).
medico( 'Francisco','Análises Clínicas','Psiquiatria','Hospital Privado' ).

%  Extensão do predicado utente: U(utente),S(serviço),E(especialidade),I(instituição) --> {V,F}.
utente( 'Rui', 'Urgência', 'Cardiologia', 'Hospital de Braga' ).
utente( 'Diana', 'Urgência', 'Cardiologia', 'Hospital de Braga' ).
utente( 'Rita', 'Urgência', 'Cardiologia', 'Hospital de Braga' ).
utente( 'José', 'Urgência', 'Cardiologia', 'Hospital de Braga' ).
utente( 'Vera', 'Análises Clínicas', 'Psiquiatria', 'Hospital Privado' ).
utente( 'Marco', 'Análises Clínicas', 'Psiquiatria', 'Hospital Privado' ).

%  Extensão do predicado consulta: U(utente),M(medico),S(serviço),E(especialidade),I(instituição),DD(dia da data),MD(mês da data),AD(ano da data) --> {V,F}.
consulta('Rui','André','Urgência','Cardiologia','Hospital de Braga',10,10,2016).
consulta('Rui','Maria','Urgência', 'Cardiologia', 'Hospital de Braga',15,11,2016).
consulta('Diana','André','Urgência','Cardiologia','Hospital de Braga',10,10,2016).
consulta('José','Maria','Urgência','Cardiologia','Hospital de Braga',10,10,2016).
consulta('Vera','Francisco','Análises Clínicas','Psiquiatria','Hospital Privado',25,05,2015).
consulta('Rui','André','Urgência','Cardiologia','Hospital de Braga',17,07,2014).
consulta('Marco','Francisco','Análises Clínicas','Psiquiatria','Hospital Privado',17,07,2014).
consulta('Marco','Francisco','Análises Clínicas','Psiquiatria','Hospital Privado',14,02,2013).
consulta('José','Maria','Urgência','Cardiologia','Hospital de Braga',17,07,2015).

% Extensão do predicado ut_ser_inst: LU,S,I --> {V,F}.
ut_ser_inst( LU,S,I ):- 
	setof( U,S^I^utente( U,S,E,I ),LU ).

% Extensão do predicado medico_esp: LM1, E --> {V,F}.
medico_esp( LM1,E ) :- 
	setof( M,S^E^I^medico( M,S,E,I ),LM1 ).

% Extensão do predicado medico_ser: LM2, S -->{V,F}.
medico_ser( LM2,S ) :- 
	setof( M,S^E^I^medico( M,S,E,I ),LM2 ).

% Extensão do predicado med_consulta_data: LM,DD,MD,AD --> {V,F}.
med_consulta_data(LM,DD,MD,AD):- 
	setof(M,U^S^E^I^DD^MD^AD^consulta(U,M,S,E,I,DD,MD,AD),LM).

% Extensão do predicado ute_consulta_data: LU,DD,MD,AD --> {V,F}.
ute_consulta_data(LU,DD,MD,AD):- 
	setof(U,M^S^E^I^DD^MD^AD^consulta(U,M,S,E,I,DD,MD,AD),LU).

%Extensão do predicado nom_medicos_int: U,A1,M1,A2,M2,X --> {V,F}.
nom_medicos_int(U,A1,M1,A2,M2,X):- 
	findall(M,(consulta(U,M,S,E,I,DD,MD,AD),intervalo(A1,M1,A2,M2,AD,MD)),X).

%Extensão do predicado nom_serv_int: U,A1,M1,A2,M2,X --> {V,F}.
nom_serv_int(U,A1,M1,A2,M2,X):- 
	findall(S,(consulta(U,M,S,E,I,DD,MD,AD),intervalo(A1,M1,A2,M2,AD,MD)),X).

%Extensao do predicado intervalo: A1,M1,A2,M2,AD,MD  -->{V,F}.
intervalo(A1,_,A2,_,AD,_) :-
    A1<AD,
    AD<A2.

intervalo(A1,M1,A2, _,AD,MD) :-
    A1=AD,
    AD<A2,
    M1=<MD.

intervalo(A1, _,A2,M2,AD,MD) :-
    A1<AD,
    AD=A2,
    MD=<M2.

intervalo(A1,M1,A2,M2,AD,MD) :-
    A1=AD,
    AD=A2,
    M1=<MD,
    MD=<M2.

% Extensão do predicado mconje: LE,LM -->{V,F}.
mconje(LE,LM) :- findall(M,(medico(M,S,E,I),pertence(E,LE)),LM).

% Extensão do predicado pertence: X,L -->{V,F}.
pertence(X,[X|L]).
pertence(X,[Y|L]):- X\==Y , pertence(X,L).

%Extensao do predicado sem_cons: X,DD,MD,AD --> {V,F}.
sem_cons(X,DD,MD,AD):- 
	findall(M,medico( M,S,E,I ),L1),
	findall(M,consulta(U,M,S,E,I,DD,MD,AD),LM),
	subtrair(L1,LM,X).

%Extensao do predicado sem_cons_int: X,A1,M1,A2,M2 --> {V,F}.
sem_cons_int(X,A1,M1,A2,M2) :- 
	findall(M,medico( M,S,E,I ),L1),
	findall(M,(consulta(U,M,S,E,I,DD,MD,AD),intervalo(A1,M1,A2,M2,AD,MD)),LM),
	subtrair(L1,LM,X).	

%Extensao do predicado subtrair os elementos de uma lista repetidos numa outra lista: L1,L2,L -> {V,F}
subtrair([], _, []) :- !.
subtrair([A|C], B, D) :-
	pertence(A,B),
	subtrair(C, B, D).
subtrair([A|C], B, [A|D]) :-
	nao( pertence(A,B) ),
   	subtrair(C, B, D).

%Extensão do predicado registar: Termo --> {V,F}.
registar( Termo ) :-
    solucoes( Invariante,+Termo::Invariante,Lista ),
    insercao( Termo ),
    teste( Lista ).

%Extensão do predicado teste: Lista --> {V,F}.
teste( [] ).
teste( [R|LR] ) :- R , teste( LR ).

%Extensão do predicado insercao: Termo --> {V,F}.
insercao( Termo ) :- 
	assert( Termo ).
insercao( Termo ) :- 
	retract( Termo ), ! , fail.

%Extensão do predicado solucoes: Termo --> {V,F}.
solucoes( X,Y,Z ) :- 
	findall( X,Y,Z ).

%Extensão do predicado remover: Termo --> {V,F}.
remover( Termo ) :- 
	solucoes( Invariante,-Termo::Invariante,Lista ) , 
	teste( Lista ) , 
	remocao( Termo ).

%Extensão do predicado remocao: Termo --> {V,F}.
remocao( Termo ) :- 
	retract( Termo ).

%invariantes

% Extensão do predicado comprimento: L,R -->{V,F}.
comprimento([],0).
comprimento([X|L],N):- comprimento(L,R) , N is R+1.

%invariante estruturais
% Invariante Estrutural: nao permitir a insercao de consultas repetidas.
+consulta(U,M,S,E,I,DD,MD,AD)::(findall((U,M,S,E,I,DD,MD,AD),consulta(U,M,S,E,I,DD,MD,AD),Con),comprimento(Con,L),L=<1).

% Invariante Estrutural:  nao permitir a insercao de médicos repetidos.
+medico(M,S,E,I)::(findall((M,S,E,I),medico(M,S,E,I),Con),comprimento(Con,L),L=<1).

% Invariante Estrutural:  nao permitir a insercao de utentes repetidos.
+utente(U,S,E,I)::(findall((U,S,E,I),utente(U,S,E,I),Con),comprimento(Con,L),L=<1).

% Invariante Estrutural:  nao permitir a insercao de serviços repetidos.
+servico(S,E,I)::(findall((S,E,I),servico(S,E,I),Con),comprimento(Con,L),L=<1).

%invariantes referenciais
%Invariante Referencial: nao permite remover utente se ele não estiver associado a um médico nas consultas.
-utente(U,S,E,I)::(findall(M,consulta(U,M,S,E,I,DD,MD,AD),Con),comprimento(Con,L),L==0).

%Invariante Referencial: nao permite remover medico se ele não estiver associado a um utente nas consultas.
-medico(M,S,E,I)::(findall(U,consulta(U,M,S,E,I,DD,MD,AD),Con),comprimento(Con,L),L==0).

%Invariante Referencial: nao permite remover serviço que esteja associado a medicos.
-servico(S,E,I)::(findall(M,medico(M,S,E,I),Con),comprimento(Con,L),L==0).

%Invariante Referencial: nao permite remover serviços que estejam associado a utentes.
-servico(S,E,I)::(findall(U,utente(U,S,E,I),Con),comprimento(Con,L),L==0).

% Invariante Referencial: nao admite um serviço cuja especialidade não existe dentro de uma instituiçao.
+servico(S,E,I)::(especialidade(E,I)).

% Invariante Referencial: nao admite um medico cujo serviço não se encontra exatamente descrito na base de conhecimento.
+medico(M,S,E,I)::(servico(S,E,I)).

% Invariante Referencial: nao admite um utente que pertença a um serviço que não se encontra exatamente descrito na base de conhecimento.
+utente(U,S,E,I)::(servico(S,E,I)).

% Invariante Referencial: nao admite uma consulta cujos médico e utente não estejam exatamente descritos na base de conhecimento.
+consulta(U,M,S,E,I,DD,MD,AD)::(medico(M,S,E,I),utente(U,S,E,I)).


%Novas funcionalidades
%Extensão do predicado procura_data: LMU,DD,MD,AD -->{V,F}.
procura_data(LMU,DD,MD,AD):- 
	setof((M,U),U^M^S^E^I^DD^MD^AD^consulta(U,M,S,E,I,DD,MD,AD),LMU).

%Extensão do predicado elimina_repeticoes: LR,LN -->{V,F}.
elimina_repeticoes( [A|[]],[A] ).
elimina_repeticoes( [A|B],C ) :- 
	pertence( A,B ) , 
	elimina_repeticoes( B,C ).
elimina_repeticoes( [A|B],[A|C] ) :- 
	nao( pertence( A,B ) ) , 
	elimina_repeticoes( B,C ).

% Extensão do predicado não: Q -->{V,F}
nao(Q) :- 
	Q, !, fail.
nao(Q).

%Extensão do predicado med_consulta_data_rep: LM,DD,MD,AD  --> {V,F}.
med_consulta_data_rep(LM,DD,MD,AD):- 
	findall(M, consulta(U,M,S,E,I,DD,MD,AD),LM1), 
	elimina_repeticoes(LM1,LM).

% Extensão do predicado conta: X,T,N --> {V,F}.
conta(_, [], 0) :- !. 
conta(X, [X|T], N) :- 
    conta(X, T, N2), 
    N is N2 + 1.     
conta(X, [Y|T], N) :- 
    X \= Y,          
    conta(X, T, N).

% Extensão do predicado quantos_cons: M3,N,A1,M1,A2,M2 --> {V,F}.
quantos_cons(M3,N,A1,M1,A2,M2):-    
	findall(M,(consulta(U,M,S,E,I,DD,MD,AD),intervalo(A1,M1,A2,M2,AD,MD)),X),
	conta(M3,X,N).

% Invariante das novas funcionalidades. Não deixa introduzir Cirurgia no Hospital Privado.
+especialidade(E,I)::(findall(E,(especialidade(E,I),E=='Cirurgia',I=='Hospital Privado'),Con),comprimento(Con,L),L==0).





							 