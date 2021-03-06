\documentclass[a4paper]{article}
\usepackage[a4paper,left=3cm,right=2cm,top=2.5cm,bottom=2.5cm]{geometry}
\usepackage{palatino}
\usepackage[colorlinks=true,linkcolor=blue,citecolor=blue]{hyperref}
\usepackage{graphicx}
\usepackage{cp2021t}
\usepackage{subcaption}
\usepackage{adjustbox}
\usepackage{color}
\definecolor{red}{RGB}{255,  0,  0}
\definecolor{blue}{RGB}{0,0,255}
\def\red{\color{red}}
\def\blue{\color{blue}}
%================= local x=====================================================%
\def\getGif#1{\includegraphics[width=0.3\textwidth]{cp2021t_media/#1.png}}
\let\uk=\emph
\def\aspas#1{``#1"}
%================= lhs2tex=====================================================%
%include polycode.fmt
%format (div (x)(y)) = x "\div " y
%format succ = "\succ "
%format ==> = "\Longrightarrow "
%format map = "\map "
%format length = "\length "
%format fst = "\p1"
%format p1  = "\p1"
%format snd = "\p2"
%format p2  = "\p2"
%format Left = "i_1"
%format Right = "i_2"
%format i1 = "i_1"
%format i2 = "i_2"
%format >< = "\times"
%format >|<  = "\bowtie "
%format |-> = "\mapsto"
%format . = "\comp "
%format .=?=. = "\mathbin{\stackrel{\mathrm{?}}{=}}"
%format (kcomp (f)(g)) = f "\kcomp " g
%format -|- = "+"
%format conc = "\mathsf{conc}"
%format summation = "{\sum}"
%format (either (a) (b)) = "\alt{" a "}{" b "}"
%format (frac (a) (b)) = "\frac{" a "}{" b "}"
%format (uncurry f) = "\uncurry{" f "}"
%format (const f) = "\underline{" f "}"
%format TLTree = "\mathsf{TLTree}"
%format (lcbr (x)(y)) = "\begin{lcbr}" x "\\" y "\end{lcbr}"
%format (split (x) (y)) = "\conj{" x "}{" y "}"
%format (for (f) (i)) = "\for{" f "}\ {" i "}"
%format B_tree = "\mathsf{B}\mbox{-}\mathsf{tree} "
\def\ana#1{\mathopen{[\!(}#1\mathclose{)\!]}}
%format <$> = "\mathbin{\mathopen{\langle}\$\mathclose{\rangle}}"
%format (cataA (f) (g)) = "\cata{" f "~" g "}_A"
%format (anaA (f) (g)) = "\ana{" f "~" g "}_A"
%format (cataB (f) (g)) = "\cata{" f "~" g "}_B"
%format (cata (f)) = "\cata{" f "}"
%format (anaB (f) (g)) = "\ana{" f "~" g "}_B"
%format Either a b = a "+" b
%format fmap = "\mathsf{fmap}"
%format NA   = "\textsc{na}"
%format NB   = "\textsc{nb}"
%format inT = "\mathsf{in}"
%format outT = "\mathsf{out}"
%format Null = "1"
%format (Prod (a) (b)) = a >< b
%format fF = "\fun F "
%format e1 = "e_1 "
%format e2 = "e_2 "
%format Dist = "\fun{Dist}"
%format IO = "\fun{IO}"
%format BTree = "\fun{BTree} "
%format LTree = "\mathsf{LTree}"
%format inNat = "\mathsf{in}"
%format (cataNat (g)) = "\cata{" g "}"
%format Nat0 = "\N_0"
%format Rational = "\Q "
%format toRational = " to_\Q "
%format fromRational = " from_\Q "
%format muB = "\mu "
%format (frac (n)(m)) = "\frac{" n "}{" m "}"
%format (fac (n)) = "{" n "!}"
%format (underbrace (t) (p)) = "\underbrace{" t "}_{" p "}"
%format matrix = "matrix"
%%format (bin (n) (k)) = "\Big(\vcenter{\xymatrix@R=1pt{" n "\\" k "}}\Big)"
%format `ominus` = "\mathbin{\ominus}"
%format % = "\mathbin{/}"
%format <-> = "{\,\leftrightarrow\,}"
%format <|> = "{\,\updownarrow\,}"
%format `minusNat`= "\mathbin{-}"
%format ==> = "\Rightarrow"
%format .==>. = "\Rightarrow"
%format .<==>. = "\Leftrightarrow"
%format .==. = "\equiv"
%format .<=. = "\leq"
%format .&&&. = "\wedge"
%format cdots = "\cdots "
%format pi = "\pi "
%format (curry (f)) = "\overline{" f "}"
%format (cataLTree (x)) = "\llparenthesis\, " x "\,\rrparenthesis"
%format (anaLTree (x)) = "\mathopen{[\!(}" x "\mathclose{)\!]}"
%format delta = "\Delta "

%---------------------------------------------------------------------------

\title{
       	C??lculo de Programas
\\
       	Trabalho Pr??tico
\\
       	MiEI+LCC --- 2020/21
}

\author{
       	\dium
\\
       	Universidade do Minho
}


\date\mydate

\makeindex
\newcommand{\rn}[1]{\textcolor{red}{#1}}
\begin{document}

\maketitle

\begin{center}\large
\begin{tabular}{ll}
\textbf{Grupo} nr. & 5
\\\hline
a89615 & Sofia Santos
\\
a93196 & Rita Lino
\\
a93216 & Guilherme Fernandes
\end{tabular}
\end{center}

\section{Pre??mbulo}

\CP\ tem como objectivo principal ensinar
a progra\-ma????o de computadores como uma disciplina cient??fica. Para isso
parte-se de um repert??rio de \emph{combinadores} que formam uma ??lgebra da
programa????o (conjunto de leis universais e seus corol??rios) e usam-se esses
combinadores para construir programas \emph{composicionalmente}, isto ??,
agregando programas j?? existentes.

Na sequ??ncia pedag??gica dos planos de estudo dos dois cursos que t??m
esta disciplina, opta-se pela aplica????o deste m??todo ?? programa????o
em \Haskell\ (sem preju??zo da sua aplica????o a outras linguagens
funcionais). Assim, o presente trabalho pr??tico coloca os
alunos perante problemas concretos que dever??o ser implementados em
\Haskell.  H?? ainda um outro objectivo: o de ensinar a documentar
programas, a valid??-los e a produzir textos t??cnico-cient??ficos de
qualidade.

\section{Documenta????o} Para cumprir de forma integrada os objectivos
enunciados acima vamos recorrer a uma t??cnica de programa\-????o dita
``\litp{liter??ria}'' \cite{Kn92}, cujo princ??pio base ?? o seguinte:
%
\begin{quote}\em Um programa e a sua documenta????o devem coincidir.
\end{quote}
%
Por outras palavras, o c??digo fonte e a documenta????o de um
programa dever??o estar no mesmo ficheiro.

O ficheiro \texttt{cp2021t.pdf} que est?? a ler ?? j?? um exemplo de
\litp{programa????o liter??ria}: foi gerado a partir do texto fonte
\texttt{cp2021t.lhs}\footnote{O suffixo `lhs' quer dizer
\emph{\lhaskell{literate Haskell}}.} que encontrar?? no
\MaterialPedagogico\ desta disciplina descompactando o ficheiro
\texttt{cp2021t.zip} e executando:
\begin{Verbatim}[fontsize=\small]
    $ lhs2TeX cp2021t.lhs > cp2021t.tex
    $ pdflatex cp2021t
\end{Verbatim}
em que \href{https://hackage.haskell.org/package/lhs2tex}{\texttt\LhsToTeX} ??
um pre-processador que faz ``pretty printing''
de c??digo Haskell em \Latex\ e que deve desde j?? instalar executando
\begin{Verbatim}[fontsize=\small]
    $ cabal install lhs2tex --lib
\end{Verbatim}
Por outro lado, o mesmo ficheiro \texttt{cp2021t.lhs} ?? execut??vel e cont??m
o ``kit'' b??sico, escrito em \Haskell, para realizar o trabalho. Basta executar
\begin{Verbatim}[fontsize=\small]
    $ ghci cp2021t.lhs
\end{Verbatim}

%if False
\begin{code}
{-# OPTIONS_GHC -XNPlusKPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable, FlexibleInstances #-}
module Main where
import Cp
import List hiding (fac)
import Nat
import LTree
import Data.List hiding (find)
import Test.QuickCheck hiding ((><),choose,collect)
import qualified Test.QuickCheck as QuickCheck
import Graphics.Gloss
import Graphics.Gloss.Interface.Pure.Game
import Control.Monad
import Control.Applicative hiding ((<|>))
import System.Process
\end{code}
%endif

\noindent Abra o ficheiro \texttt{cp2021t.lhs} no seu editor de texto preferido
e verifique que assim ??: todo o texto que se encontra dentro do ambiente
\begin{quote}\small\tt
\verb!\begin{code}!
\\ ... \\
\verb!\end{code}!
\end{quote}
?? seleccionado pelo \GHCi\ para ser executado.

\section{Como realizar o trabalho}
Este trabalho te??rico-pr??tico deve ser realizado por grupos de 3 (ou 4) alunos.
Os detalhes da avalia????o (datas para submiss??o do relat??rio e sua defesa
oral) s??o os que forem publicados na \cp{p??gina da disciplina} na \emph{internet}.

Recomenda-se uma abordagem participativa dos membros do grupo
de trabalho por forma a poderem responder ??s quest??es que ser??o colocadas
na \emph{defesa oral} do relat??rio.

Em que consiste, ent??o, o \emph{relat??rio} a que se refere o par??grafo anterior?
?? a edi????o do texto que est?? a ser lido, preenchendo o anexo \ref{sec:resolucao}
com as respostas. O relat??rio dever?? conter ainda a identifica????o dos membros
do grupo de trabalho, no local respectivo da folha de rosto.

Para gerar o PDF integral do relat??rio deve-se ainda correr os comando seguintes,
que actualizam a bibliografia (com \Bibtex) e o ??ndice remissivo (com \Makeindex),
\begin{Verbatim}[fontsize=\small]
    $ bibtex cp2021t.aux
    $ makeindex cp2021t.idx
\end{Verbatim}
e recompilar o texto como acima se indicou. Dever-se-?? ainda instalar o utilit??rio
\QuickCheck,
que ajuda a validar programas em \Haskell\ e a biblioteca \gloss{Gloss} para
gera????o de gr??ficos 2D:
\begin{Verbatim}[fontsize=\small]
    $ cabal install QuickCheck gloss --lib
\end{Verbatim}
Para testar uma propriedade \QuickCheck~|prop|, basta invoc??-la com o comando:
\begin{verbatim}
    > quickCheck prop
    +++ OK, passed 100 tests.
\end{verbatim}
Pode-se ainda controlar o n??mero de casos de teste e sua complexidade,
como o seguinte exemplo mostra:
\begin{verbatim}
    > quickCheckWith stdArgs { maxSuccess = 200, maxSize = 10 } prop
    +++ OK, passed 200 tests.
\end{verbatim}
Qualquer programador tem, na vida real, de ler e analisar (muito!) c??digo
escrito por outros. No anexo \ref{sec:codigo} disponibiliza-se algum
c??digo \Haskell\ relativo aos problemas que se seguem. Esse anexo dever??
ser consultado e analisado ?? medida que isso for necess??rio.

\subsection{Stack}

O \stack{Stack} ?? um programa ??til para criar, gerir e manter projetos em \Haskell.
Um projeto criado com o Stack possui uma estrutura de pastas muito espec??fica:

\begin{itemize}
\item Os m??dulos auxiliares encontram-se na pasta \emph{src}.
\item O m??dulos principal encontra-se na pasta \emph{app}.
\item A lista de dep??ndencias externas encontra-se no ficheiro \emph{package.yaml}.
\end{itemize}

Pode aceder ao \GHCi\ utilizando o comando:
\begin{verbatim}
stack ghci
\end{verbatim}

Garanta que se encontra na pasta mais externa \textbf{do projeto}.
A primeira vez que correr este comando as dep??ndencias externas ser??o instaladas automaticamente.

Para gerar o PDF, garanta que se encontra na diretoria \emph{app}.

\Problema

Os \emph{tipos de dados alg??bricos} estudados ao longo desta disciplina oferecem
uma grande capacidade expressiva ao programador. Gra??as ?? sua flexibilidade,
torna-se trivial implementar \DSL s
e at?? mesmo \href{http://www.cse.chalmers.se/~ulfn/papers/thesis.pdf}{linguagens de programa????o}.

Paralelamente, um t??pico bastante estudado no ??mbito de \DL\
?? a deriva????o autom??tica de express??es matem??ticas, por exemplo, de derivadas.
Duas t??cnicas que podem ser utilizadas para o c??lculo de derivadas s??o:

\begin{itemize}
\item \emph{Symbolic differentiation}
\item \emph{Automatic differentiation}
\end{itemize}

\emph{Symbolic differentiation} consiste na aplica????o sucessiva de transforma????es
(leia-se: fun????es) que sejam congruentes com as regras de deriva????o. O resultado
final ser?? a express??o da derivada.

O leitor atento poder?? notar um problema desta t??cnica: a express??o
inicial pode crescer de forma descontrolada, levando a um c??lculo pouco eficiente.
\emph{Automatic differentiation} tenta resolver este problema,
calculando \textbf{o valor} da derivada da express??o em todos os passos.
Para tal, ?? necess??rio calcular o valor da express??o \textbf{e} o valor da sua derivada.

Vamos de seguida definir uma linguagem de express??es matem??ticas simples e
implementar as duas t??cnicas de deriva????o autom??tica.
Para isso, seja dado o seguinte tipo de dados,

\begin{code}
data ExpAr a = X
           | N a
           | Bin BinOp (ExpAr a) (ExpAr a)
           | Un UnOp (ExpAr a)
           deriving (Eq, Show)
\end{code}

\noindent
onde |BinOp| e |UnOp| representam opera????es bin??rias e un??rias, respectivamente:

\begin{code}
data BinOp = Sum
           | Product
           deriving (Eq, Show)

data UnOp = Negate
          | E
          deriving (Eq, Show)
\end{code}

\noindent
O construtor |E| simboliza o exponencial de base $e$.

Assim, cada express??o pode ser uma vari??vel, um n??mero, uma opera????o bin??ria
aplicada ??s devidas express??es, ou uma opera????o un??ria aplicada a uma express??o.
Por exemplo,
\begin{spec}
Bin Sum X (N 10)
\end{spec}
designa |x+10| na nota????o matem??tica habitual.

\begin{enumerate}
\item A defini????o das fun????es |inExpAr| e |baseExpAr| para este tipo ?? a seguinte:
\begin{code}
inExpAr = either (const X) num_ops where
  num_ops = either N ops
  ops     = either bin (uncurry Un)
  bin(op, (a, b)) = Bin op a b

baseExpAr f g h j k l z = f -|- (g -|- (h >< (j >< k) -|- l >< z))
\end{code}

  Defina as fun????es |outExpAr| e |recExpAr|,
  e teste as propriedades que se seguem.
  \begin{propriedade}
    |inExpAr| e |outExpAr| s??o testemunhas de um isomorfismo,
    isto ??,
    |inExpAr . outExpAr = id| e |outExpAr . idExpAr = id|:
\begin{code}
prop_in_out_idExpAr :: (Eq a) => ExpAr a -> Bool
prop_in_out_idExpAr = inExpAr . outExpAr .==. id

prop_out_in_idExpAr :: (Eq a) => OutExpAr a -> Bool
prop_out_in_idExpAr = outExpAr . inExpAr .==. id
\end{code}
    \end{propriedade}

  \item Dada uma express??o aritm??tica e um escalar para substituir o |X|,
	a fun????o

\begin{quote}
      |eval_exp :: Floating a => a -> (ExpAr a) -> a|
\end{quote}

\noindent calcula o resultado da express??o. Na p??gina \pageref{pg:P1}
    esta fun????o est?? expressa como um catamorfismo. Defina o respectivo gene
    e, de seguida, teste as propriedades:
    \begin{propriedade}
       A fun????o |eval_exp| respeita os elementos neutros das opera????es.
\begin{code}
prop_sum_idr :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_sum_idr a exp = eval_exp a exp .=?=. sum_idr where
  sum_idr = eval_exp a (Bin Sum exp (N 0))

prop_sum_idl :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_sum_idl a exp = eval_exp a exp .=?=. sum_idl where
  sum_idl = eval_exp a (Bin Sum (N 0) exp)

prop_product_idr :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_product_idr a exp = eval_exp a exp .=?=. prod_idr where
  prod_idr = eval_exp a (Bin Product exp (N 1))

prop_product_idl :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_product_idl a exp = eval_exp a exp .=?=. prod_idl where
  prod_idl = eval_exp a (Bin Product (N 1) exp)

prop_e_id :: (Floating a, Real a) => a -> Bool
prop_e_id a = eval_exp a (Un E (N 1)) == expd 1

prop_negate_id :: (Floating a, Real a) => a -> Bool
prop_negate_id a = eval_exp a (Un Negate (N 0)) == 0
\end{code}
    \end{propriedade}
    \begin{propriedade}
      Negar duas vezes uma express??o tem o mesmo valor que n??o fazer nada.
\begin{code}
prop_double_negate :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_double_negate a exp = eval_exp a exp .=?=. eval_exp a (Un Negate (Un Negate exp))
\end{code}
    \end{propriedade}

  \item ?? poss??vel otimizar o c??lculo do valor de uma express??o aritm??tica tirando proveito
  dos elementos absorventes de cada opera????o. Implemente os genes da fun????o
\begin{spec}
      optmize_eval :: (Floating a, Eq a) => a -> (ExpAr a) -> a
\end{spec}
  que se encontra na p??gina \pageref{pg:P1} expressa como um hilomorfismo\footnote{Qual ?? a vantagem de implementar a fun????o |optimize_eval| utilizando um hilomorfismo em vez de utilizar um catamorfismo com um gene "inteligente"?}
  e teste as propriedades:

    \begin{propriedade}
      A fun????o |optimize_eval| respeita a sem??ntica da fun????o |eval|.
\begin{code}
prop_optimize_respects_semantics :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_optimize_respects_semantics a exp = eval_exp a exp .=?=. optmize_eval a exp
\end{code}
    \end{propriedade}


\item Para calcular a derivada de uma express??o, ?? necess??rio aplicar transforma????es
?? express??o original que respeitem as regras das derivadas:\footnote{%
	Apesar da adi????o e multiplica????o gozarem da propriedade comutativa,
	h?? que ter em aten????o a ordem das opera????es por causa dos testes.}

\begin{itemize}
  \item Regra da soma:
\begin{eqnarray*}
	\frac{d}{dx}(f(x)+g(x))=\frac{d}{dx}(f(x))+\frac{d}{dx}(g(x))
\end{eqnarray*}
  \item Regra do produto:
\begin{eqnarray*}
	\frac{d}{dx}(f(x)g(x))=f(x)\cdot \frac{d}{dx}(g(x))+\frac{d}{dx}(f(x))\cdot g(x)
\end{eqnarray*}
\end{itemize}

  Defina o gene do catamorfismo que ocorre na fun????o
    \begin{quote}
      |sd :: Floating a => ExpAr a -> ExpAr a|
    \end{quote}
  que, dada uma express??o aritm??tica, calcula a sua derivada.
  Testes a fazer, de seguida:
    \begin{propriedade}
       A fun????o |sd| respeita as regras de deriva????o.
\begin{code}
prop_const_rule :: (Real a, Floating a) => a -> Bool
prop_const_rule a = sd (N a) == N 0

prop_var_rule :: Bool
prop_var_rule = sd X == N 1

prop_sum_rule :: (Real a, Floating a) => ExpAr a -> ExpAr a -> Bool
prop_sum_rule exp1 exp2 = sd (Bin Sum exp1 exp2) == sum_rule where
  sum_rule = Bin Sum (sd exp1) (sd exp2)

prop_product_rule :: (Real a, Floating a) => ExpAr a -> ExpAr a -> Bool
prop_product_rule exp1 exp2 = sd (Bin Product exp1 exp2) == prod_rule where
  prod_rule =Bin Sum (Bin Product exp1 (sd exp2)) (Bin Product (sd exp1) exp2)

prop_e_rule :: (Real a, Floating a) => ExpAr a -> Bool
prop_e_rule exp = sd (Un E exp) == Bin Product (Un E exp) (sd exp)

prop_negate_rule :: (Real a, Floating a) => ExpAr a -> Bool
prop_negate_rule exp = sd (Un Negate exp) == Un Negate (sd exp)
\end{code}
    \end{propriedade}

\item Como foi visto, \emph{Symbolic differentiation} n??o ?? a t??cnica
mais eficaz para o c??lculo do valor da derivada de uma express??o.
\emph{Automatic differentiation} resolve este problema c??lculando o valor
da derivada em vez de manipular a express??o original.

  Defina o gene do catamorfismo que ocorre na fun????o
    \begin{spec}
    ad :: Floating a => a -> ExpAr a -> a
    \end{spec}
  que, dada uma express??o aritm??tica e um ponto,
  calcula o valor da sua derivada nesse ponto,
  sem transformar manipular a express??o original.
  Testes a fazer, de seguida:

    \begin{propriedade}
       Calcular o valor da derivada num ponto |r| via |ad| ?? equivalente a calcular a derivada da express??o e avalia-la no ponto |r|.
\begin{code}
prop_congruent :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_congruent a exp = ad a exp .=?=. eval_exp a (sd exp)
\end{code}
    \end{propriedade}
\end{enumerate}

\Problema

Nesta disciplina estudou-se como fazer \pd{programa????o din??mica} por c??lculo,
recorrendo ?? lei de recursividade m??tua.\footnote{Lei (\ref{eq:fokkinga})
em \cite{Ol18}, p??gina \pageref{eq:fokkinga}.}

Para o caso de fun????es sobre os n??meros naturais (|Nat0|, com functor |fF
X = 1 + X|) ?? f??cil derivar-se da lei que foi estudada uma
	\emph{regra de algibeira}
	\label{pg:regra}
que se pode ensinar a programadores que n??o tenham estudado
\cp{C??lculo de Programas}. Apresenta-se de seguida essa regra, tomando como exemplo o
c??lculo do ciclo-\textsf{for} que implementa a fun????o de Fibonacci, recordar
o sistema
\begin{spec}
fib 0 = 1
fib(n+1) = f n

f 0 = 1
f (n+1) = fib n + f n
\end{spec}
Obter-se-?? de imediato
\begin{code}
fib' = p1 . for loop init where
   loop(fib,f)=(f,fib+f)
   init = (1,1)
\end{code}
usando as regras seguintes:
\begin{itemize}
\item	O corpo do ciclo |loop| ter?? tantos argumentos quanto o n??mero de fun????es mutuamente recursivas.
\item	Para as vari??veis escolhem-se os pr??prios nomes das fun????es, pela ordem
que se achar conveniente.\footnote{Podem obviamente usar-se outros s??mbolos, mas numa primeira leitura
d?? jeito usarem-se tais nomes.}
\item	Para os resultados v??o-se buscar as express??es respectivas, retirando a vari??vel |n|.
\item	Em |init| coleccionam-se os resultados dos casos de base das fun????es, pela mesma ordem.
\end{itemize}
Mais um exemplo, envolvendo polin??mios do segundo grau $ax^2 + b x + c$ em |Nat0|.
Seguindo o m??todo estudado nas aulas\footnote{Sec????o 3.17 de \cite{Ol18} e t??pico
\href{https://www4.di.uminho.pt/~jno/media/cp/}{Recursividade m??tua} nos v??deos das aulas te??ricas.},
de $f\ x = a x^2 + b x + c$ derivam-se duas fun????es mutuamente recursivas:
\begin{spec}
f 0 = c
f (n+1) = f n + k n

k 0 = a + b
k(n+1) = k n + 2 a
\end{spec}
Seguindo a regra acima, calcula-se de imediato a seguinte implementa????o, em Haskell:
\begin{code}
f' a b c = p1 . for loop init where
  loop(f,k) = (f+k,k+2*a)
  init = (c,a+b)
\end{code}
O que se pede ent??o, nesta pergunta?
Dada a f??rmula que d?? o |n|-??simo \catalan{n??mero de Catalan},
\begin{eqnarray}
	C_n = \frac{(2n)!}{(n+1)! (n!) }
	\label{eq:cat}
\end{eqnarray}
derivar uma implementa????o de $C_n$ que n??o calcule factoriais nenhuns.
Isto ??, derivar um ciclo-\textsf{for}
\begin{spec}
cat = cdots . for loop init where cdots
\end{spec}
que implemente esta fun????o.

\begin{propriedade}
A fun????o proposta coincidem com a defini????o dada:
\begin{code}
prop_cat = (>=0) .==>. (catdef  .==. cat)
\end{code}
\end{propriedade}
%
\textbf{Sugest??o}: Come??ar por estudar muito bem o processo de c??lculo dado
no anexo \ref{sec:recmul} para o problema (semelhante) da fun????o exponencial.


\Problema

As \bezier{curvas de B??zier}, designa????o dada em honra ao engenheiro
\href{https://en.wikipedia.org/wiki/Pierre_B%C3%A9zier}{Pierre B??zier},
s??o curvas ub??quas na ??rea de computa????o gr??fica, anima????o e modela????o.
Uma curva de B??zier ?? uma curva param??trica, definida por um conjunto
$\{P_0,...,P_N\}$ de pontos de controlo, onde $N$ ?? a ordem da curva.

\begin{figure}[h!]
  \centering
  \includegraphics[width=0.8\textwidth]{cp2021t_media/Bezier_curves.png}
  \caption{Exemplos de curvas de B??zier retirados da \bezier{ Wikipedia}.}
\end{figure}

O algoritmo de \emph{De Casteljau} ?? um m??todo recursivo capaz de calcular
curvas de B??zier num ponto. Apesar de ser mais lento do que outras abordagens,
este algoritmo ?? numericamente mais est??vel, trocando velocidade por corre????o.

De forma sucinta, o valor de uma curva de B??zier de um s?? ponto $\{P_0\}$
(ordem $0$) ?? o pr??prio ponto $P_0$. O valor de uma curva de B??zier de ordem
$N$ ?? calculado atrav??s da interpola????o linear da curva de B??zier dos primeiros
$N-1$ pontos e da curva de B??zier dos ??ltimos $N-1$ pontos.

A interpola????o linear entre 2 n??meros, no intervalo $[0, 1]$, ?? dada pela
seguinte fun????o:

\begin{code}
linear1d :: Rational -> Rational -> OverTime Rational
linear1d a b = formula a b where
  formula :: Rational -> Rational -> Float -> Rational
  formula x y t = ((1.0 :: Rational) - (toRational t)) * x + (toRational t) * y
\end{code}
%
A interpola????o linear entre 2 pontos de dimens??o $N$ ?? calculada atrav??s
da interpola????o linear de cada dimens??o.

O tipo de dados |NPoint| representa um ponto com $N$ dimens??es.
\begin{code}
type NPoint = [Rational]
\end{code}
Por exemplo, um ponto de 2 dimens??es e um ponto de 3 dimens??es podem ser
representados, respetivamente, por:
\begin{spec}
p2d = [1.2, 3.4]
p3d = [0.2, 10.3, 2.4]
\end{spec}
%
O tipo de dados |OverTime a| representa um termo do tipo |a| num dado instante
(dado por um |Float|).
\begin{code}
type OverTime a = Float -> a
\end{code}
%
O anexo \ref{sec:codigo} tem definida a fun????o
    \begin{spec}
    calcLine :: NPoint -> (NPoint -> OverTime NPoint)
    \end{spec}
que calcula a interpola????o linear entre 2 pontos, e a fun????o
    \begin{spec}
    deCasteljau :: [NPoint] -> OverTime NPoint
    \end{spec}
que implementa o algoritmo respectivo.

\begin{enumerate}

\item Implemente |calcLine| como um catamorfismo de listas,
testando a sua defini????o com a propriedade:
    \begin{propriedade} Defini????o alternativa.
\begin{code}
prop_calcLine_def :: NPoint -> NPoint -> Float -> Bool
prop_calcLine_def p q d = calcLine p q d ==  zipWithM linear1d p q d
\end{code}
    \end{propriedade}

\item Implemente a fun????o |deCasteljau| como um hilomorfismo, testando agora a propriedade:
    \begin{propriedade}
      Curvas de B??zier s??o sim??tricas.
\begin{code}
prop_bezier_sym :: [[Rational]] -> Gen Bool
prop_bezier_sym l = all (< delta) . calc_difs . bezs <$> elements ps  where
  calc_difs = (\(x, y) -> zipWith (\w v -> if w >= v then w - v else v - w) x y)
  bezs t    = (deCasteljau l t, deCasteljau (reverse l) (fromRational (1 - (toRational t))))
  delta = 1e-2
\end{code}
    \end{propriedade}

  \item Corra a fun????o |runBezier| e aprecie o seu trabalho\footnote{%
        A representa????o em Gloss ?? uma adapta????o de um
        \href{https://github.com/hrldcpr/Bezier.hs}{projeto}
        de Harold Cooper.} clicando na janela que ?? aberta (que cont??m, a verde, um ponto
        inicila) com o bot??o esquerdo do rato para adicionar mais pontos.
        A tecla |Delete| apaga o ponto mais recente.

\end{enumerate}

\Problema

Seja dada a f??rmula que calcula a m??dia de uma lista n??o vazia $x$,
\begin{equation}
avg\ x = \frac 1 k\sum_{i=1}^{k} x_i
\end{equation}
onde $k=length\ x$. Isto ??, para sabermos a m??dia de uma lista precisamos de dois catamorfismos: o que faz o somat??rio e o que calcula o comprimento a lista.
Contudo, ?? facil de ver que
\begin{quote}
	$avg\ [a]=a$
\\
	$avg (a:x) = \frac 1 {k+1}(a+\sum_{i=1}^{k} x_i) = \frac{a+k(avg\ x)}{k+1}$ para $k=length\ x$
\end{quote}
Logo $avg$ est?? em recursividade m??tua com $length$ e o par de fun????es pode ser expresso por um ??nico catamorfismo, significando que a lista apenas ?? percorrida uma vez.

\begin{enumerate}

\item	Recorra ?? lei de recursividade m??tua para derivar a fun????o
|avg_aux = cata (either b q)| tal que
|avg_aux = split avg length| em listas n??o vazias.

\item	Generalize o racioc??nio anterior para o c??lculo da m??dia de todos os elementos de uma \LTree\ recorrendo a uma ??nica travessia da ??rvore (i.e.\ catamorfismo).

\end{enumerate}
Verifique as suas fun????es testando a propriedade seguinte:
\begin{propriedade}
A m??dia de uma lista n??o vazia e de uma \LTree\ com os mesmos elementos coincide,
a menos de um erro de 0.1 mil??simas:
\begin{code}
prop_avg :: [Double] -> Property
prop_avg = nonempty .==>. diff .<=. const 0.000001 where
   diff l = avg l - (avgLTree . genLTree) l
   genLTree = anaLTree lsplit
   nonempty = (>[])
\end{code}
\end{propriedade}

\Problema	(\textbf{NB}: Esta quest??o ?? \textbf{opcional} e funciona como \textbf{valoriza????o} apenas para os alunos que desejarem faz??-la.)

\vskip 1em \noindent
Existem muitas linguagens funcionais para al??m do \Haskell, que ?? a linguagem usada neste trabalho pr??tico. Uma delas ?? o \Fsharp\ da Microsoft. Na directoria \verb!fsharp! encontram-se os m??dulos \Cp, \Nat\ e \LTree\ codificados em \Fsharp. O que se pede ?? a biblioteca \BTree\ escrita na mesma linguagem.

Modo de execu????o: o c??digo que tiverem produzido nesta pergunta deve ser colocado entre o \verb!\begin{verbatim}! e o \verb!\end{verbatim}! da correspondente parte do anexo \ref{sec:resolucao}. Para al??m disso, os grupos podem demonstrar o c??digo na oral.

\newpage

\part*{Anexos}

\appendix

\section{Como exprimir c??lculos e diagramas em LaTeX/lhs2tex}
Como primeiro exemplo, estudar o texto fonte deste trabalho para obter o
efeito:\footnote{Exemplos tirados de \cite{Ol18}.}
\begin{eqnarray*}
\start
	|id = split f g|
%
\just\equiv{ universal property }
%
        |lcbr(
		p1 . id = f
	)(
		p2 . id = g
	)|
%
\just\equiv{ identity }
%
        |lcbr(
		p1 = f
	)(
		p2 = g
	)|
\qed
\end{eqnarray*}

Os diagramas podem ser produzidos recorrendo ?? \emph{package} \LaTeX\
\href{https://ctan.org/pkg/xymatrix}{xymatrix}, por exemplo:
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |Nat0|
           \ar[d]_-{|cataNat g|}
&
    |1 + Nat0|
           \ar[d]^{|id + (cataNat g)|}
           \ar[l]_-{|inNat|}
\\
     |B|
&
     |1 + B|
           \ar[l]^-{|g|}
}
\end{eqnarray*}

\section{Programa????o din??mica por recursividade m??ltipla}\label{sec:recmul}
Neste anexo d??o-se os detalhes da resolu????o do Exerc??cio \ref{ex:exp} dos apontamentos da
disciplina\footnote{Cf.\ \cite{Ol18}, p??gina \pageref{ex:exp}.},
onde se pretende implementar um ciclo que implemente
o c??lculo da aproxima????o at?? |i=n| da fun????o exponencial $exp\ x = e^x$,
via s??rie de Taylor:
\begin{eqnarray}
	exp\ x
& = &
	\sum_{i=0}^{\infty} \frac {x^i} {i!}
\end{eqnarray}
Seja $e\ x\ n = \sum_{i=0}^{n} \frac {x^i} {i!}$ a fun????o que d?? essa aproxima????o.
?? f??cil de ver que |e x 0 = 1| e que $|e x (n+1)| = |e x n| + \frac {x^{n+1}} {(n+1)!}$.
Se definirmos $|h x n| = \frac {x^{n+1}} {(n+1)!}$ teremos |e x| e |h x| em recursividade
m??tua. Se repetirmos o processo para |h x n| etc obteremos no total tr??s fun????es nessa mesma
situa????o:
\begin{spec}
e x 0 = 1
e x (n+1) = h x n + e x n

h x 0 = x
h x (n+1) = x/(s n) * h x n

s 0 = 2
s (n+1) = 1 + s n
\end{spec}
Segundo a \emph{regra de algibeira} descrita na p??gina \ref{pg:regra} deste enunciado,
ter-se-??, de imediato:
\begin{code}
e' x = prj . for loop init where
     init = (1,x,2)
     loop(e,h,s)=(h+e,x/s*h,1+s)
     prj(e,h,s) = e
\end{code}

\section{C??digo fornecido}\label{sec:codigo}

\subsection*{Problema 1}

\begin{code}
expd :: Floating a => a -> a
expd = Prelude.exp

type OutExpAr a = Either () (Either a (Either (BinOp, (ExpAr a, ExpAr a)) (UnOp, ExpAr a)))
\end{code}

\subsection*{Problema 2}
Defini????o da s??rie de Catalan usando factoriais (\ref{eq:cat}):
\begin{code}
catdef n = div (fac((2*n))) ((fac((n+1))*(fac n)))
\end{code}
Or??culo para inspec????o dos primeiros 26 n??meros de Catalan\footnote{Fonte:
\catalan{Wikipedia}.}:
\begin{code}
oracle = [
    1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, 208012, 742900, 2674440, 9694845,
    35357670, 129644790, 477638700, 1767263190, 6564120420, 24466267020,
    91482563640, 343059613650, 1289904147324, 4861946401452
    ]
\end{code}

\subsection*{Problema 3}
Algoritmo:
\begin{spec}
deCasteljau :: [NPoint] -> OverTime NPoint
deCasteljau [] = nil
deCasteljau [p] = const p
deCasteljau l = \pt -> (calcLine (p pt) (q pt)) pt where
  p = deCasteljau (init l)
  q = deCasteljau (tail l)
\end{spec}
Fun????o auxiliar:
\begin{spec}
calcLine :: NPoint -> (NPoint -> OverTime NPoint)
calcLine [] = const nil
calcLine(p:x) = curry g p (calcLine x) where
   g :: (Rational, NPoint -> OverTime NPoint) -> (NPoint -> OverTime NPoint)
   g (d,f) l = case l of
       []     -> nil
       (x:xs) -> \z -> concat $ (sequenceA [singl . linear1d d x, f xs]) z
\end{spec}
2D:
\begin{code}
bezier2d :: [NPoint] -> OverTime (Float, Float)
bezier2d [] = const (0, 0)
bezier2d l = \z -> (fromRational >< fromRational) . (\[x, y] -> (x, y)) $ ((deCasteljau l) z)
\end{code}
Modelo:
\begin{code}
data World = World { points :: [NPoint]
                   , time :: Float
                   }
initW :: World
initW = World [] 0

tick :: Float -> World -> World
tick dt world = world { time=(time world) + dt }

actions :: Event -> World -> World
actions (EventKey (MouseButton LeftButton) Down _ p) world =
  world {points=(points world) ++ [(\(x, y) -> map toRational [x, y]) p]}
actions (EventKey (SpecialKey KeyDelete) Down _ _) world =
    world {points = cond (== []) id init (points world)}
actions _ world = world

scaleTime :: World -> Float
scaleTime w = (1 + cos (time w)) / 2

bezier2dAtTime :: World -> (Float, Float)
bezier2dAtTime w = (bezier2dAt w) (scaleTime w)

bezier2dAt :: World -> OverTime (Float, Float)
bezier2dAt w = bezier2d (points w)

thicCirc :: Picture
thicCirc = ThickCircle 4 10

ps :: [Float]
ps = map fromRational ps' where
  ps' :: [Rational]
  ps' = [0, 0.01..1] -- interval
\end{code}
Gloss:
\begin{code}
picture :: World -> Picture
picture world = Pictures
  [ animateBezier (scaleTime world) (points world)
  , Color white . Line . map (bezier2dAt world) $ ps
  , Color blue . Pictures $ [Translate (fromRational x) (fromRational y) thicCirc | [x, y] <- points world]
  , Color green $ Translate cx cy thicCirc
  ] where
  (cx, cy) = bezier2dAtTime world
\end{code}
Anima????o:
\begin{code}
animateBezier :: Float -> [NPoint] -> Picture
animateBezier _ [] = Blank
animateBezier _ [_] = Blank
animateBezier t l = Pictures
  [ animateBezier t (init l)
  , animateBezier t (tail l)
  , Color red . Line $ [a, b]
  , Color orange $ Translate ax ay thicCirc
  , Color orange $ Translate bx by thicCirc
  ] where
  a@(ax, ay) = bezier2d (init l) t
  b@(bx, by) = bezier2d (tail l) t
\end{code}
Propriedades e \emph{main}:
\begin{code}
runBezier :: IO ()
runBezier = play (InWindow "B??zier" (600, 600) (0,  0))
  black 50 initW picture actions tick

runBezierSym :: IO ()
runBezierSym = quickCheckWith (stdArgs {maxSize = 20, maxSuccess = 200} ) prop_bezier_sym
\end{code}

Compila????o e execu????o dentro do interpretador:\footnote{Pode ser ??til em testes
envolvendo \gloss{Gloss}. Nesse caso, o teste em causa deve fazer parte de uma fun????o
|main|.}
\begin{code}
main = runBezier

run = do { system "ghc cp2021t" ; system "./cp2021t" }
\end{code}

\subsection*{QuickCheck}
C??digo para gera????o de testes:
\begin{code}
instance Arbitrary UnOp where
  arbitrary = elements [Negate, E]

instance Arbitrary BinOp where
  arbitrary = elements [Sum, Product]

instance (Arbitrary a) => Arbitrary (ExpAr a) where
  arbitrary = do
    binop <- arbitrary
    unop  <- arbitrary
    exp1  <- arbitrary
    exp2  <- arbitrary
    a     <- arbitrary

    frequency . map (id >< pure) $ [(20, X), (15, N a), (35, Bin binop exp1 exp2), (30, Un unop exp1)]


infixr 5 .=?=.
(.=?=.) :: Real a => a -> a -> Bool
(.=?=.) x y = (toRational x) == (toRational y)


\end{code}

\subsection*{Outras fun????es auxiliares}
%----------------- Outras defini????es auxiliares -------------------------------------------%
L??gicas:
\begin{code}
infixr 0 .==>.
(.==>.) :: (Testable prop) => (a -> Bool) -> (a -> prop) -> a -> Property
p .==>. f = \a -> p a ==> f a

infixr 0 .<==>.
(.<==>.) :: (a -> Bool) -> (a -> Bool) -> a -> Property
p .<==>. f = \a -> (p a ==> property (f a)) .&&. (f a ==> property (p a))

infixr 4 .==.
(.==.) :: Eq b => (a -> b) -> (a -> b) -> (a -> Bool)
f .==. g = \a -> f a == g a

infixr 4 .<=.
(.<=.) :: Ord b => (a -> b) -> (a -> b) -> (a -> Bool)
f .<=. g = \a -> f a <= g a

infixr 4 .&&&.
(.&&&.) :: (a -> Bool) -> (a -> Bool) -> (a -> Bool)
f .&&&. g = \a -> ((f a) && (g a))
\end{code}

%----------------- Solu????es dos alunos -----------------------------------------%

\section{Solu????es dos alunos}\label{sec:resolucao}
Os alunos devem colocar neste anexo as suas solu????es para os exerc??cios
propostos, de acordo com o "layout" que se fornece. N??o podem ser
alterados os nomes ou tipos das fun????es dadas, mas pode ser adicionado
texto, disgramas e/ou outras fun????es auxiliares que sejam necess??rias.

Valoriza-se a escrita de \emph{pouco} c??digo que corresponda a solu????es
simples e elegantes.

\subsection*{Problema 1} \label{pg:P1}
S??o dadas:
\begin{code}
cataExpAr g = g . recExpAr (cataExpAr g) . outExpAr
anaExpAr g = inExpAr . recExpAr (anaExpAr g) . g
hyloExpAr h g = cataExpAr h . anaExpAr g

eval_exp :: Floating a => a -> (ExpAr a) -> a
eval_exp a = cataExpAr (g_eval_exp a)

optmize_eval :: (Floating a, Eq a) => a -> (ExpAr a) -> a
optmize_eval a = hyloExpAr (gopt a) clean

sd :: Floating a => ExpAr a -> ExpAr a
sd = p2 . cataExpAr sd_gen

ad :: Floating a => a -> ExpAr a -> a
ad v = p2 . cataExpAr (ad_gen v)
\end{code}

\subsubsection*{outExpAr}
\begin{eqnarray*}
\start
  |out . in = id|
%
\just\equiv{|in = either (const X) num_ops|, fus??o-+}
%
  |either (out . const X) (out . num_ops) = id|
%
\just\equiv{universal-+, natural-id}
%
  |lcbr(
        out . const X = i1
  )(
        out . num_ops = i2
  )|
%
\just\equiv{|num_ops = either N ops|, fus??o-+}
%
  |lcbr(
        out . const X = i1
  )(
        either (out . N) (out . ops) = i2
  )|
%
\just\equiv{universal-+}
%
  |lcbr(
        out . const X = i1
  )(
        lcbr(
             out . N = i2 . i1
        )(
             out . ops = i2 . i2
        )
  )|
%
\just\equiv{|ops = either bin (uncurry Un)|, fus??o-+}
%
  |lcbr(
        out . const X = i1
  )(
        lcbr(
             out . N = i2 . i1
        )(
             either (out . bin) (uncurry Un) = i2 . i2
        )
  )|
%
\just\equiv{universal-+}
%
  |lcbr(
        out . const X = i1
  )(
        lcbr(
             out . N = i2 . i1
        )(
             lcbr(
                  out . bin = i2 . i2 . i1
             )(
                  out . uncurry Un = i2 . i2 . i2
             )
        )
  )|
%
\just\equiv{pointwise, def-comp}
%
  |lcbr(
        out (const X x) = i1 x
  )(
        lcbr(
             out (N x) = i2 (i1 x)
        )(
             lcbr(
                  out (bin (op, (a, b))) = i2 (i2 (i1 (op, (a, b))))
             )(
                  out (uncurry Un (op, a)) = (i2 (i2 (i2 (op, a))))
             )
        )
  )|
%
\just\equiv{def-const, |bin (op, (a, b)) = Bin op a b|, uncurry}
%
  |lcbr(
        out X = i1 ()
  )(
        lcbr(
             out (N x) = i2 (i1 x)
        )(
             lcbr(
                  out (Bin op a b) = i2 (i2 (i1 (op, (a, b))))
             )(
                  out (Un op a) = (i2 (i2 (i2 (op, a))))
             )
        )
  )|
\qed
\end{eqnarray*}
\\
\begin{code}
outExpAr X = i1 ()
outExpAr (N x) = (i2 . i1) x
outExpAr (Bin op a b) = (i2 . i2 . i1) (op, (a, b))
outExpAr (Un op a) = (i2 . i2 . i2) (op, a)
\end{code}

\subsubsection*{recExpAr}
\begin{code}
recExpAr f = baseExpAr id id id f f id f
\end{code}

\subsubsection*{g\_eval\_exp}
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |ExpAr A|
           \ar[d]_-{|eval_exp a|}
           \ar@@/^/[r]^-{|outT|}_-\cong
&
    |1 + (A + ((BinOp >< (ExpAr A)|^2| + UnOp >< ExpAr A))|
           \ar[d]^{|id + (id + (id >< (eval_exp a)|^2| + id >< (eval_exp a)))|}
           \ar@@/^/[l]^-{|inT|}
\\
     |A|
&
     |1 + (A + (BinOp >< A|^2| + Unop >< A))|
           \ar[l]^-{|g_eval_exp a|}
}
\end{eqnarray*}

\begin{code}
g_eval_exp x = either (const x) (either id (either (uncurry binOp) (uncurry unOp)))
  where
    binOp Sum = uncurry (+)
    binOp Product = uncurry (*)
    unOp Negate = negate
    unOp E = expd
\end{code}

\subsubsection*{hyloExpAr}

\begin{eqnarray*}
\xymatrix@@C=2cm{
   |ExpAr A|
          \ar[d]_-{\ana{clean}}
          \ar@@/_5pc/[dd]_-{\llbracket |gopt a, clean| \rrbracket}
           \ar[r]^-{|clean|}
&
   |1 + ( A + (BinOp >< (ExpAr A)|^2| + UnOp >< ExpAr A))|
          \ar[d]^{|id + (id + (id >< |\ana{|clean|}^2| + |\ana{|id >< clean|})}
\\
    |ExpAr A|
          \ar[d]_-{|cata (gopt a)|}
           \ar@@/^/[r]^-{|outT|}_-\cong
&
   |1 + (A + (BinOp >< (ExpAr A)|^2| + UnOp >< ExpAr A))|
          \ar@@/^/[l]^-{|inT|}
          \ar[d]^{|id + (id + (id >< (cata (gopt a))|^2| + id >< cata (gopt a))|}
\\
    |A|
&
   |1 + (A + (BinOp >< A|^2| + UnOp >< A))|
          \ar[l]^-{|gopt a|}
}
\end{eqnarray*}

A vantagem de usarmos um hilomorfismo ?? que assim podemos optimizar a express??o antes e depois de substituir a vari??vel.\\
\textbf{NB}: Esta fun????o n??o passa nalguns testes do |quickCheck|, uma vez que a |eval_exp| nalguns casos d?? |NaN|,
enquanto que a |optmize_eval| n??o.

\subsubsection*{clean}
\begin{code}
clean (Bin Sum (N 0) x) = outExpAr x
clean (Bin Sum x (N 0)) = outExpAr x
clean (Bin Product (N 0) _) = outExpAr (N 0)
clean (Bin Product _ (N 0)) = outExpAr (N 0)
clean (Bin Product (N 1) x) = outExpAr x
clean (Bin Product x (N 1)) = outExpAr x
clean (Un E (N 0)) = outExpAr (N 1)
clean (Un Negate (Un Negate x)) = outExpAr x
clean x = outExpAr x
\end{code}

\subsubsection*{gopt}
\begin{code}
gopt _ (Right (Right (Left (Sum, (0, x))))) = x
gopt _ (Right (Right (Left (Sum, (x, 0))))) = x
gopt _ (Right (Right (Left (Product, (0, _))))) = 0
gopt _ (Right (Right (Left (Product, (_, 0))))) = 0
gopt _ (Right (Right (Left (Product, (1, x))))) = x
gopt _ (Right (Right (Left (Product, (x, 1))))) = x
gopt _ (Right (Right (Right (E, 0)))) = 1
gopt _ (Right (Right (Right (Negate, 0)))) = 0
gopt a b = g_eval_exp a b
\end{code}

\subsubsection*{sd\_gen}
\begin{code}
sd_gen :: Floating a =>
    Either ()
           (Either a
                   (Either (BinOp, ((ExpAr a, ExpAr a), (ExpAr a, ExpAr a)))
                           (UnOp, (ExpAr a, ExpAr a))))
    -> (ExpAr a, ExpAr a)
sd_gen = either (const (X, N 1)) (either n (either binOp unOp))
  where
    n a = (N a, N 0)
    binOp (op, ((f, f'), (g, g'))) =
      let x = Bin op f g in
        case op of
          Sum -> (x, Bin Sum f' g')
          Product -> (x, Bin Sum (Bin Product f g') (Bin Product f' g))
    unOp (op, (f, f')) =
      let x = Un op f in
        case op of
          E -> (x, Bin Product (Un E f) f')
          Negate -> (x, Un Negate f')
\end{code}

\subsubsection*{ad\_gen}
\begin{code}
ad_gen x = either (const (x, 1)) (either (split id (fromInteger . zero)) (either binOp unOp))
  where
    binOp (op, ((f, f'), (g, g'))) =
      case op of
        Sum -> (f + g, f' + g')
        _ -> (f * g, f * g' + f' * g)
    unOp (op, (f, f')) =
      case op of
        E -> (expd f, expd f * f')
        _ -> (negate f, negate f')
\end{code}

\subsubsection*{show}
\begin{code}
showExpAr :: Show a => ExpAr a -> String
showExpAr = cataExpAr gene
  where
    gene = either (const "x") (either show (either showBinOp showUnOp))
    showBinOp (Sum, (a, b)) = "(" ++ a ++ " + " ++ b ++ ")"
    showBinOp (Product, (a, b)) = "(" ++ a ++ " * " ++ b ++ ")"
    showUnOp (E, a) = "e^" ++ a
    showUnOp (Negate, a) = "(-" ++ a ++ ")"
\end{code}

\subsection*{Problema 2}
Definir
\begin{code}
inic = (1,2,2)
loop(c,d,e) = (div (c * d) e, d + 4, e + 1)
prj(c,d,e) = c
\end{code}
por forma a que
\begin{code}
cat = prj . for loop inic
\end{code}
seja a fun????o pretendida.
\textbf{NB}: usar divis??o inteira.
Apresentar de seguida a justifica????o da solu????o encontrada.

\bigskip

A partir da f??rmula \ref{eq:cat}, que d?? o \textit{n}-??simo n??mero de Catalan,
somos capazes de definir uma fun????o $ c\ n = \frac{(2n)!}{(n+1)!(n!)}$.
Vemos facilmente que esta fun????o pode ser definida recursivamente
por $c\ 0 = 1$ e $c\ (n + 1) = c\ n * \frac{2(2n+1)}{n+2}$.
Se definirmos $d\ n = 2(2n+1)$ e $e\ n = n + 2$,
obtemos as seguintes fun????es:

\begin{spec}
c 0 = 1
c (n + 1) = div (c n * d n) (e n)

d 0 = 2
d (n + 1) = d n + 4

e 0 = 2
e (n + 1) = e n + 1
\end{spec}

Podemos agora aplicar a \textit{regra da algibeira}
descrita na p??gina \ref{pg:regra} e definir as fun????es necess??rias ??
resolu????o do problema.

\textbf{NB}: Como estamos a usar divis??o inteira, ?? importante que
na fun????o $c$ fa??amos a multiplica????o antes da divis??o. Caso contr??rio,
a fun????o n??o dar?? valores corretos, pois ir?? arredondar o resultado da
divis??o.

\subsection*{Problema 3}

Sabendo que $ calcLine = \cata{h} $, somos capazes de derivar a defini????o
de $ h $ a partir da defini????o de $ calcLine $.

\begin{eqnarray*}
\start
%
        |lcbr(
		calcLine [] = const nil
	)(
		calcLine (p : x) = curry g p (calcLine x)
	)|
%
\just\equiv{ def-cons, def-nil, def-curry }
%
        |lcbr(
		calcLine (nil x) = const nil
	)(
		calcLine (cons (p, x)) = g (p,(calcLine x))
	)|
%
\just\equiv{ def-x }
%
        |lcbr(
		calcLine (nil x) = const nil
	)(
		calcLine (cons (p, x)) = g ((id >< calcLine) (p, x))
	)|
%
\just\equiv{ def-comp, def-const }
%
        |lcbr(
		(calcLine . nil) x = (const (const nil)) x
	)(
		(calcLine . cons) (p, x) = (g . (id >< calcLine)) (p, x)
	)|
%
\just\equiv{ igualdade extensional }
%
        |lcbr(
		calcLine . nil = const (const nil)
	)(
		calcLine . cons = g . (id >< calcLine)
	)|
%
\just\equiv{ eq-+ }
%
  |[calcLine . nil, calcLine . cons] = [const (const nil), g . (id >< calcLine)]|
%
\just\equiv{ fus??o-+, absor????o-+ }
%
  |calcLine . [nil, cons] = [const (const nil), g] . (id + id >< calcLine)|
%
\just\equiv{ universal-cata}
%
  |calcLine = cata [const (const nil), g] |
%
\just\equiv{ calcLine = $ \cata{h} $ }
%
  |h = [const (const nil), g]|
\qed
\end{eqnarray*}

% `f xs` d??-nos o resultado de aplicar calcLine ??s caudas das duas listas introduzidas
% `linear1d d x` calcula a interpola????o linear das cabe??as das listas
% Visto que `f xs` ?? do tipo `OverTime NPoint` e `linear1d d x` ?? do tipo `OverTime Rational`, ?? necess??rio converter o segundo resultado para o tipo do 1??
% Para isso, usamos a fun????o `singl`
% Depois, a fun????o `sequenceA` converte uma lista de `OverTime NPoint` para um `OverTime [NPoint]`
% Finalmente, o `concat` concatena a lista de `NPoint`, visto que isto ?? uma lista de listas, num simples `NPoint`
% Temos agora o resultado pretendido, com o tipo `OverTime NPoint`

\begin{code}
calcLine :: NPoint -> NPoint -> OverTime NPoint
calcLine = cataList h where
  h = either (const (const nil)) g
  g :: (Rational,NPoint -> OverTime NPoint) -> NPoint -> OverTime NPoint
  g (d,f) l = case l of
    [] -> nil
    (x:xs) -> concat . sequenceA [singl . linear1d d x, f xs]
\end{code}

Pela an??lise da defini????o do algoritmo de \textit{De Casteljau} fornecida, vemos que esta divide a lista que lhe ?? dada nos seus elementos constituintes,
fazendo depois uma jun????o (\textit{"merge"}) destes elementos usando a fun????o \texttt{calcLine}. Podemos assim concluir que o hilomorfismo a definir ter??
como estrutura interm??dia uma LTree, onde cada folha representa um NPoint, obtido ap??s N divis??es da lista inicial. ?? f??cil de verificar que este
algoritmo ?? bastante semelhante ao conhecido \textit{merge sort}, cujo hilomorfismo tamb??m usa uma LTree como estrutura interm??dia.

Assim, o anamorfismo \texttt{coalg} dever?? formar uma LTree a partir da lista de \textit{input}, usando o mesmo m??todo que a defini????o fornecida para
o algoritmo, ou seja, "enviando" para o ramo esquerdo a lista sem o ??ltimo valor e para o ramo direito a lista sem o primeiro valor. Se a lista apenas tiver um valor,
criamos uma folha com esse valor.

Por outro lado, o catamorfismo \texttt{alg} dever??, para cada elemento da LTree, juntar os seus dois ramos usando a fun????o \texttt{calcLine} que definimos acima.
Se este elemento for uma folha, visto que n??o tem ramos, o catamorfismo devolve-a envolvida num \texttt{const}, j?? que deve devolver algo do tipo
\texttt{OverTime NPoint} e um ??nico NPoint (o valor armazenado na folha) n??o ir?? sofrer altera????es com o tempo, logo ter?? que ser constante.

Temos assim uma defini????o para o hilomorfismo, apresentada a seguir:

\begin{eqnarray*}
\xymatrix@@C=2cm{
   |[NPoint]|
          \ar[d]_-{\ana{coalg}}
          \ar@@/_5pc/[dd]_-{\llbracket |alg, coalg| \rrbracket}
           \ar[r]^-{|coalg|}
&
   |NPoint + [NPoint]|^2
          \ar[d]^{|id + |\ana{coalg}^2}
\\
    |LTree NPoint|
          \ar[d]_-{|cata alg|}
           \ar@@/^/[r]^-{|outT|}_-\cong
&
   |NPoint + (LTree NPoint)|^2
          \ar@@/^/[l]^-{|inT|}
          \ar[d]^{|id + (cata alg)|^2}
\\
    |OverTime NPoint|
&
   |NPoint + (OverTime NPoint)|^2
          \ar[l]^-{|alg|}
}
\end{eqnarray*}
\newpage
\begin{code}
deCasteljau :: [NPoint] -> OverTime NPoint
deCasteljau [] = const []
deCasteljau l = hyloAlgForm alg coalg l where
   coalg [p] = i1 p
   coalg l = i2 (init l, tail l)
   alg = either const mergeL
   mergeL (l, m) = \t -> calcLine (l t) (m t) t

hyloAlgForm = hyloLTree
\end{code}

\subsection*{Problema 4}
\subsubsection*{Solu????o para listas n??o vazias:}

Sabendo que | cata (either b q) = split avg length |, geram-se os diagramas
de $ avg $ e de $ length $ para se poder recorrer ?? recursividade m??tua.

\begin{eqnarray*}
\start
%
	|cata (either b q) = (split avg length)|
%
\just\equiv{ universal cata }
%
  |split avg length = (either b q) . fF (split avg length)|
%
\qed
\end{eqnarray*}


\begin{eqnarray*}
\xymatrix@@C=2cm{
    |A|^{+}
           \ar[d]_-{|avg|}
           \ar@@/^/[r]^-{|outT|}_-\cong
&
    |A + A ><| A^{+}
           \ar[d]^{|id + id >< split avg length |}
           \ar@@/^/[l]^-{|inT|}
\\
     |A|
&
     |A + A >< (A >< Nat0)|
           \ar[l]^-{|either id f |}
}
&
\xymatrix@@C=2cm{
    |A|^{+}
           \ar[d]_-{length}
           \ar@@/^/[r]^-{|outT|}_-\cong
&
    |A + A ><| A^{+}
           \ar[d]^{|id + id >< split avg length |}
           \ar@@/^/[l]^-{|inT|}
\\
     |Nat0|
&
     |A + A >< (A >< Nat0)|
           \ar[l]^-{|either (const 1) (succ . p2 . p2 |}
}
\end{eqnarray*}

\begin{code}
avg = p1.avg_aux
\end{code}

\begin{code}
recL f = id -|- id >< f

outL [a] = i1 a
outL (a:l) = i2 (a, l)

inL = either singl cons

cataL g = g . recL (cataL g) . outL
\end{code}

\begin{code}
avg_aux = cataL $ either b q
  where
    b = split id (const 1)
    q = split f (succ . p2 . p2)
    f (a, (avg, k)) = (a + k * avg) / (k + 1)
\end{code}
\subsubsection*{Solu????o para ??rvores de tipo \LTree:}

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |LTree A|
           \ar[d]_-{|avg|}
           \ar@@/^/[r]^-{|outT|}_-\cong
&
    |A + (LTree A|)^{2}
           \ar[d]^{|id + (split avg length)|^{2}}
           \ar@@/^/[l]^-{|inT|}
\\
     |A|
&
     |A + A >< (A >< Nat0)|
           \ar[l]^-{|either id h |}
}
&
\xymatrix@@C=2cm{
    |LTree A|
           \ar[d]_-{length}
           \ar@@/^/[r]^-{|outT|}_-\cong
&
    |A + (LTree A|)^{2}
           \ar[d]^{|id + (split avg length)|^{2}}
           \ar@@/^/[l]^-{|inT|}
\\
     |Nat0|
&
     |A + A >< (A >< Nat0)|
           \ar[l]^-{|either (const 1) k |}
}
\end{eqnarray*}

\begin{code}
avgLTree = p1.cataLTree gene where
   gene = either b q
    where
      b = split id (const 1)
      q ((a1, l1), (a2, l2)) = ((a1 * l1 + a2 * l2) / (l1 + l2), l1 + l2)
\end{code}

\subsection*{Problema 5}
Inserir em baixo o c??digo \Fsharp\ desenvolvido, entre \verb!\begin{verbatim}! e \verb!\end{verbatim}!:

\subsubsection*{Datatype definition}
\begin{verbatim}
type BTree<'a> =
  | Empty
  | Node of 'a * (BTree<'a> * BTree<'a>)

let inBTree x = either (konst Empty) Node x

let outBTree x =
  match x with
    | Empty -> i1 ()
    | Node (a, (l, r)) -> i2 (a, (l, r))
\end{verbatim}

\subsubsection*{Ana + cata + hylo}
\begin{verbatim}
let baseBTree f g x = (id -|- (f >< (g >< g))) x

let recBTree g x = (baseBTree id g) x

let rec cataBTree g x = (g << (recBTree (cataBTree g)) << outBTree) x

let rec anaBTree g x = (inBTree << (recBTree (anaBTree g) ) << g) x

let hyloBTree f g x = (cataBTree f << anaBTree g) x
\end{verbatim}

\subsubsection*{Map}
\begin{verbatim}
let fmap f x = cataBTree (inBTree << baseBTree f id) x
\end{verbatim}

\subsubsection*{Examples}

\paragraph*{Inversion (mirror)}
\begin{verbatim}
let invBTree x = cataBTree (inBTree << (id -|- (id >< swap))) x
\end{verbatim}

\paragraph*{Counting}
\begin{verbatim}
let countBTree x = cataBTree (either (konst 0) (succ << (uncurry (+)) << p2)) x
\end{verbatim}

\paragraph*{Serilization}

\subparagraph*{in-order traversal}
\begin{verbatim}
let inord x =
  let join (a, (l, r)) = l @ a::r
  in either nil join x

let inordt x = cataBTree inord x
\end{verbatim}

\subparagraph*{pre-order traversal}
\begin{verbatim}
let preord x =
  let join (a, (l, r)) = a::l @ r
  in either nil join x

let preordt x = cataBTree preord x
\end{verbatim}

\subparagraph*{post-order traversal}
\begin{verbatim}
let postord x =
  let join (a, (l, r)) = l @ r @ [a]
  in either nil join x

let postordt x = cataBTree postord x
\end{verbatim}

\paragraph*{Quicksort}
\begin{verbatim}
let rec part p l =
  match l with
    | [] -> ([], [])
    | (h::t) ->
      let (s, l) = part p t
      in
        if p h then
          (h::s, l)
        else
          (s, h::l)

let qsep l =
  match l with
    | [] -> i1 ()
    | (h :: t) ->
      let (s, l) = part ((<) h) t
      in i2 (h, (s, l))

let qSort x = hyloBTree inord qsep x
\end{verbatim}

\paragraph*{Traces}
\begin{verbatim}
let rec delete x y =
  match y with
    | [] -> []
    | (h::t) ->
      if x = h then t
      else h :: delete x t

let union x y = x @ List.fold (flip delete) (List.distinct y) x

let tunion (a, (l, r)) = union (List.map ((@) [a]) l) (List.map ((@) [a]) r)

let traces x = cataBTree (either (konst [[]]) tunion) x
\end{verbatim}

\paragraph*{Towers of Hanoi}
\begin{verbatim}
let present x = inord x

let strategy (d, n) =
  match n with
    | 0 -> i1 ()
    | otherwise -> i2 ((n, d), ((not d, n), (not d, n)))

let hanoi x = hyloBTree present strategy x
\end{verbatim}

\subsubsection*{Depth and balancing (using mutual recursion)}
\begin{verbatim}
let baldepth x =
  let f ((b1, d1), (b2, d2)) = ((b1, b2), (d1, d2))
  let h (a, ((b1, b2), (d1, d2))) =
      (b1 && b2 && abs (d1 - d2) <= 1, 1 + max d1 d2)
  let g x = either (konst (true, 1)) (h << (id >< f)) x
  in cataBTree g x

let balBTree b = (p1 << baldepth) b

let depthBTree b = (p2 << baldepth) b
\end{verbatim}

%----------------- Fim do anexo com solu????es dos alunos ------------------------%

%----------------- ??ndice remissivo (exige makeindex) -------------------------%

\printindex

%----------------- Bibliografia (exige bibtex) --------------------------------%

\bibliographystyle{plain}
\bibliography{cp2021t}

%----------------- Fim do documento -------------------------------------------%
\end{document}
