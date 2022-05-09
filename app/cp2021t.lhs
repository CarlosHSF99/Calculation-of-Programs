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
       	Cálculo de Programas
\\
       	Trabalho Prático
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
\textbf{Grupo} nr. & 119
\\\hline
a89492 & Ivo Pereira Vilas Boas
\\
a89509 & Carlos Humberto da Silva Ferreira
\\
a89555 & Diogo Francisco Lima Barbosa
\\
a90439 & Nuno Gonçalo Machado Rodrigues
\end{tabular}
\end{center}

\section{Preâmbulo}

\CP\ tem como objectivo principal ensinar
a progra\-mação de computadores como uma disciplina científica. Para isso
parte-se de um repertório de \emph{combinadores} que formam uma álgebra da
programação (conjunto de leis universais e seus corolários) e usam-se esses
combinadores para construir programas \emph{composicionalmente}, isto é,
agregando programas já existentes.

Na sequência pedagógica dos planos de estudo dos dois cursos que têm
esta disciplina, opta-se pela aplicação deste método à programação
em \Haskell\ (sem prejuízo da sua aplicação a outras linguagens
funcionais). Assim, o presente trabalho prático coloca os
alunos perante problemas concretos que deverão ser implementados em
\Haskell.  Há ainda um outro objectivo: o de ensinar a documentar
programas, a validá-los e a produzir textos técnico-científicos de
qualidade.

\section{Documentação} Para cumprir de forma integrada os objectivos
enunciados acima vamos recorrer a uma técnica de programa\-ção dita
``\litp{literária}'' \cite{Kn92}, cujo princípio base é o seguinte:
%
\begin{quote}\em Um programa e a sua documentação devem coincidir.
\end{quote}
%
Por outras palavras, o código fonte e a documentação de um
programa deverão estar no mesmo ficheiro.

O ficheiro \texttt{cp2021t.pdf} que está a ler é já um exemplo de
\litp{programação literária}: foi gerado a partir do texto fonte
\texttt{cp2021t.lhs}\footnote{O suffixo `lhs' quer dizer
\emph{\lhaskell{literate Haskell}}.} que encontrará no
\MaterialPedagogico\ desta disciplina descompactando o ficheiro
\texttt{cp2021t.zip} e executando:
\begin{Verbatim}[fontsize=\small]
    $ lhs2TeX cp2021t.lhs > cp2021t.tex
    $ pdflatex cp2021t
\end{Verbatim}
em que \href{https://hackage.haskell.org/package/lhs2tex}{\texttt\LhsToTeX} é
um pre-processador que faz ``pretty printing''
de código Haskell em \Latex\ e que deve desde já instalar executando
\begin{Verbatim}[fontsize=\small]
    $ cabal install lhs2tex --lib
\end{Verbatim}
Por outro lado, o mesmo ficheiro \texttt{cp2021t.lhs} é executável e contém
o ``kit'' básico, escrito em \Haskell, para realizar o trabalho. Basta executar
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
import Control.Monad hiding (ap)
import Control.Applicative hiding ((<|>))
import System.Process
\end{code}
%endif

\noindent Abra o ficheiro \texttt{cp2021t.lhs} no seu editor de texto preferido
e verifique que assim é: todo o texto que se encontra dentro do ambiente
\begin{quote}\small\tt
\verb!\begin{code}!
\\ ... \\
\verb!\end{code}!
\end{quote}
é seleccionado pelo \GHCi\ para ser executado.

\section{Como realizar o trabalho}
Este trabalho teórico-prático deve ser realizado por grupos de 3 (ou 4) alunos.
Os detalhes da avaliação (datas para submissão do relatório e sua defesa
oral) são os que forem publicados na \cp{página da disciplina} na \emph{internet}.

Recomenda-se uma abordagem participativa dos membros do grupo
de trabalho por forma a poderem responder às questões que serão colocadas
na \emph{defesa oral} do relatório.

Em que consiste, então, o \emph{relatório} a que se refere o parágrafo anterior?
É a edição do texto que está a ser lido, preenchendo o anexo \ref{sec:resolucao}
com as respostas. O relatório deverá conter ainda a identificação dos membros
do grupo de trabalho, no local respectivo da folha de rosto.

Para gerar o PDF integral do relatório deve-se ainda correr os comando seguintes,
que actualizam a bibliografia (com \Bibtex) e o índice remissivo (com \Makeindex),
\begin{Verbatim}[fontsize=\small]
    $ bibtex cp2021t.aux
    $ makeindex cp2021t.idx
\end{Verbatim}
e recompilar o texto como acima se indicou. Dever-se-á ainda instalar o utilitário
\QuickCheck,
que ajuda a validar programas em \Haskell\ e a biblioteca \gloss{Gloss} para
geração de gráficos 2D:
\begin{Verbatim}[fontsize=\small]
    $ cabal install QuickCheck gloss --lib
\end{Verbatim}
Para testar uma propriedade \QuickCheck~|prop|, basta invocá-la com o comando:
\begin{verbatim}
    > quickCheck prop
    +++ OK, passed 100 tests.
\end{verbatim}
Pode-se ainda controlar o número de casos de teste e sua complexidade,
como o seguinte exemplo mostra:
\begin{verbatim}
    > quickCheckWith stdArgs { maxSuccess = 200, maxSize = 10 } prop
    +++ OK, passed 200 tests.
\end{verbatim}
Qualquer programador tem, na vida real, de ler e analisar (muito!) código
escrito por outros. No anexo \ref{sec:codigo} disponibiliza-se algum
código \Haskell\ relativo aos problemas que se seguem. Esse anexo deverá
ser consultado e analisado à medida que isso for necessário.

\subsection{Stack}

O \stack{Stack} é um programa útil para criar, gerir e manter projetos em \Haskell.
Um projeto criado com o Stack possui uma estrutura de pastas muito específica:

\begin{itemize}
\item Os módulos auxiliares encontram-se na pasta \emph{src}.
\item O módulos principal encontra-se na pasta \emph{app}.
\item A lista de depêndencias externas encontra-se no ficheiro \emph{package.yaml}.
\end{itemize}

Pode aceder ao \GHCi\ utilizando o comando:
\begin{verbatim}
stack ghci
\end{verbatim}

Garanta que se encontra na pasta mais externa \textbf{do projeto}.
A primeira vez que correr este comando as depêndencias externas serão instaladas automaticamente.

Para gerar o PDF, garanta que se encontra na diretoria \emph{app}.

\Problema

Os \emph{tipos de dados algébricos} estudados ao longo desta disciplina oferecem
uma grande capacidade expressiva ao programador. Graças à sua flexibilidade,
torna-se trivial implementar \DSL s
e até mesmo \href{http://www.cse.chalmers.se/~ulfn/papers/thesis.pdf}{linguagens de programação}.

Paralelamente, um tópico bastante estudado no âmbito de \DL\
é a derivação automática de expressões matemáticas, por exemplo, de derivadas.
Duas técnicas que podem ser utilizadas para o cálculo de derivadas são:

\begin{itemize}
\item \emph{Symbolic differentiation}
\item \emph{Automatic differentiation}
\end{itemize}

\emph{Symbolic differentiation} consiste na aplicação sucessiva de transformações
(leia-se: funções) que sejam congruentes com as regras de derivação. O resultado
final será a expressão da derivada.

O leitor atento poderá notar um problema desta técnica: a expressão
inicial pode crescer de forma descontrolada, levando a um cálculo pouco eficiente.
\emph{Automatic differentiation} tenta resolver este problema,
calculando \textbf{o valor} da derivada da expressão em todos os passos.
Para tal, é necessário calcular o valor da expressão \textbf{e} o valor da sua derivada.

Vamos de seguida definir uma linguagem de expressões matemáticas simples e
implementar as duas técnicas de derivação automática.
Para isso, seja dado o seguinte tipo de dados,

\begin{code}
data ExpAr a = X
           | N a
           | Bin BinOp (ExpAr a) (ExpAr a)
           | Un UnOp (ExpAr a)
           deriving (Eq, Show)
\end{code}

\noindent
onde |BinOp| e |UnOp| representam operações binárias e unárias, respectivamente:

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

Assim, cada expressão pode ser uma variável, um número, uma operação binária
aplicada às devidas expressões, ou uma operação unária aplicada a uma expressão.
Por exemplo,
\begin{spec}
Bin Sum X (N 10)
\end{spec}
designa |x+10| na notação matemática habitual.

\begin{enumerate}
\item A definição das funções |inExpAr| e |baseExpAr| para este tipo é a seguinte:
\begin{code}
inExpAr = either (const X) num_ops where
  num_ops = either N ops
  ops     = either bin (uncurry Un)
  bin(op, (a, b)) = Bin op a b

baseExpAr f g h j k l z = f -|- (g -|- (h >< (j >< k) -|- l >< z))
\end{code}

  Defina as funções |outExpAr| e |recExpAr|,
  e teste as propriedades que se seguem.
  \begin{propriedade}
    |inExpAr| e |outExpAr| são testemunhas de um isomorfismo,
    isto é,
    |inExpAr . outExpAr = id| e |outExpAr . idExpAr = id|:
\begin{code}
prop_in_out_idExpAr :: (Eq a) => ExpAr a -> Bool
prop_in_out_idExpAr = inExpAr . outExpAr .==. id

prop_out_in_idExpAr :: (Eq a) => OutExpAr a -> Bool
prop_out_in_idExpAr = outExpAr . inExpAr .==. id
\end{code}
    \end{propriedade}

  \item Dada uma expressão aritmética e um escalar para substituir o |X|,
	a função

\begin{quote}
      |eval_exp :: Floating a => a -> (ExpAr a) -> a|
\end{quote}

\noindent calcula o resultado da expressão. Na página \pageref{pg:P1}
    esta função está expressa como um catamorfismo. Defina o respectivo gene
    e, de seguida, teste as propriedades:
    \begin{propriedade}
       A função |eval_exp| respeita os elementos neutros das operações.
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
      Negar duas vezes uma expressão tem o mesmo valor que não fazer nada.
\begin{code}
prop_double_negate :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_double_negate a exp = eval_exp a exp .=?=. eval_exp a (Un Negate (Un Negate exp))
\end{code}
    \end{propriedade}

  \item É possível otimizar o cálculo do valor de uma expressão aritmética tirando proveito
  dos elementos absorventes de cada operação. Implemente os genes da função
\begin{spec}
      optmize_eval :: (Floating a, Eq a) => a -> (ExpAr a) -> a
\end{spec}
  que se encontra na página \pageref{pg:P1} expressa como um hilomorfismo\footnote{Qual é a vantagem de implementar a função |optimize_eval| utilizando um hilomorfismo em vez de utilizar um catamorfismo com um gene "inteligente"?}
  e teste as propriedades:

    \begin{propriedade}
      A função |optimize_eval| respeita a semântica da função |eval|.
\begin{code}
prop_optimize_respects_semantics :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_optimize_respects_semantics a exp = eval_exp a exp .=?=. optmize_eval a exp
\end{code}
    \end{propriedade}


\item Para calcular a derivada de uma expressão, é necessário aplicar transformações
à expressão original que respeitem as regras das derivadas:\footnote{%
	Apesar da adição e multiplicação gozarem da propriedade comutativa,
	há que ter em atenção a ordem das operações por causa dos testes.}

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

  Defina o gene do catamorfismo que ocorre na função
    \begin{quote}
      |sd :: Floating a => ExpAr a -> ExpAr a|
    \end{quote}
  que, dada uma expressão aritmética, calcula a sua derivada.
  Testes a fazer, de seguida:
    \begin{propriedade}
       A função |sd| respeita as regras de derivação.
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

\item Como foi visto, \emph{Symbolic differentiation} não é a técnica
mais eficaz para o cálculo do valor da derivada de uma expressão.
\emph{Automatic differentiation} resolve este problema cálculando o valor
da derivada em vez de manipular a expressão original.

  Defina o gene do catamorfismo que ocorre na função
    \begin{spec}
    ad :: Floating a => a -> ExpAr a -> a
    \end{spec}
  que, dada uma expressão aritmética e um ponto,
  calcula o valor da sua derivada nesse ponto,
  sem transformar manipular a expressão original.
  Testes a fazer, de seguida:

    \begin{propriedade}
       Calcular o valor da derivada num ponto |r| via |ad| é equivalente a calcular a derivada da expressão e avalia-la no ponto |r|.
\begin{code}
prop_congruent :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_congruent a exp = ad a exp .=?=. eval_exp a (sd exp)
\end{code}
    \end{propriedade}
\end{enumerate}

\Problema

Nesta disciplina estudou-se como fazer \pd{programação dinâmica} por cálculo,
recorrendo à lei de recursividade mútua.\footnote{Lei (\ref{eq:fokkinga})
em \cite{Ol18}, página \pageref{eq:fokkinga}.}

Para o caso de funções sobre os números naturais (|Nat0|, com functor |fF
X = 1 + X|) é fácil derivar-se da lei que foi estudada uma
	\emph{regra de algibeira}
	\label{pg:regra}
que se pode ensinar a programadores que não tenham estudado
\cp{Cálculo de Programas}. Apresenta-se de seguida essa regra, tomando como exemplo o
cálculo do ciclo-\textsf{for} que implementa a função de Fibonacci, recordar
o sistema
\begin{spec}
fib 0 = 1
fib(n+1) = f n

f 0 = 1
f (n+1) = fib n + f n
\end{spec}
Obter-se-á de imediato
\begin{code}
fib' = p1 . for loop init where
   loop(fib,f)=(f,fib+f)
   init = (1,1)
\end{code}
usando as regras seguintes:
\begin{itemize}
\item	O corpo do ciclo |loop| terá tantos argumentos quanto o número de funções mutuamente recursivas.
\item	Para as variáveis escolhem-se os próprios nomes das funções, pela ordem
que se achar conveniente.\footnote{Podem obviamente usar-se outros símbolos, mas numa primeira leitura
dá jeito usarem-se tais nomes.}
\item	Para os resultados vão-se buscar as expressões respectivas, retirando a variável |n|.
\item	Em |init| coleccionam-se os resultados dos casos de base das funções, pela mesma ordem.
\end{itemize}
Mais um exemplo, envolvendo polinómios do segundo grau $ax^2 + b x + c$ em |Nat0|.
Seguindo o método estudado nas aulas\footnote{Secção 3.17 de \cite{Ol18} e tópico
\href{https://www4.di.uminho.pt/~jno/media/cp/}{Recursividade mútua} nos vídeos das aulas teóricas.},
de $f\ x = a x^2 + b x + c$ derivam-se duas funções mutuamente recursivas:
\begin{spec}
f 0 = c
f (n+1) = f n + k n

k 0 = a + b
k(n+1) = k n + 2 a
\end{spec}
Seguindo a regra acima, calcula-se de imediato a seguinte implementação, em Haskell:
\begin{code}
f' a b c = p1 . for loop init where
  loop(f,k) = (f+k,k+2*a)
  init = (c,a+b)
\end{code}
O que se pede então, nesta pergunta?
Dada a fórmula que dá o |n|-ésimo \catalan{número de Catalan},
\begin{eqnarray}
	C_n = \frac{(2n)!}{(n+1)! (n!) }
	\label{eq:cat}
\end{eqnarray}
derivar uma implementação de $C_n$ que não calcule factoriais nenhuns.
Isto é, derivar um ciclo-\textsf{for}
\begin{spec}
cat = cdots . for loop init where cdots
\end{spec}
que implemente esta função.

\begin{propriedade}
A função proposta coincidem com a definição dada:
\begin{code}
prop_cat = (>=0) .==>. (catdef  .==. cat)
\end{code}
\end{propriedade}
%
\textbf{Sugestão}: Começar por estudar muito bem o processo de cálculo dado
no anexo \ref{sec:recmul} para o problema (semelhante) da função exponencial.


\Problema

As \bezier{curvas de Bézier}, designação dada em honra ao engenheiro
\href{https://en.wikipedia.org/wiki/Pierre_B%C3%A9zier}{Pierre Bézier},
são curvas ubíquas na área de computação gráfica, animação e modelação.
Uma curva de Bézier é uma curva paramétrica, definida por um conjunto
$\{P_0,...,P_N\}$ de pontos de controlo, onde $N$ é a ordem da curva.

\begin{figure}[h!]
  \centering
  \includegraphics[width=0.8\textwidth]{cp2021t_media/Bezier_curves.png}
  \caption{Exemplos de curvas de Bézier retirados da \bezier{ Wikipedia}.}
\end{figure}

O algoritmo de \emph{De Casteljau} é um método recursivo capaz de calcular
curvas de Bézier num ponto. Apesar de ser mais lento do que outras abordagens,
este algoritmo é numericamente mais estável, trocando velocidade por correção.

De forma sucinta, o valor de uma curva de Bézier de um só ponto $\{P_0\}$
(ordem $0$) é o próprio ponto $P_0$. O valor de uma curva de Bézier de ordem
$N$ é calculado através da interpolação linear da curva de Bézier dos primeiros
$N-1$ pontos e da curva de Bézier dos últimos $N-1$ pontos.

A interpolação linear entre 2 números, no intervalo $[0, 1]$, é dada pela
seguinte função:

\begin{code}
linear1d :: Rational -> Rational -> OverTime Rational
linear1d a b = formula a b where
  formula :: Rational -> Rational -> Float -> Rational
  formula x y t = ((1.0 :: Rational) - (toRational t)) * x + (toRational t) * y
\end{code}
%
A interpolação linear entre 2 pontos de dimensão $N$ é calculada através
da interpolação linear de cada dimensão.

O tipo de dados |NPoint| representa um ponto com $N$ dimensões.
\begin{code}
type NPoint = [Rational]
\end{code}
Por exemplo, um ponto de 2 dimensões e um ponto de 3 dimensões podem ser
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
O anexo \ref{sec:codigo} tem definida a função
    \begin{spec}
    calcLine :: NPoint -> (NPoint -> OverTime NPoint)
    \end{spec}
que calcula a interpolação linear entre 2 pontos, e a função
    \begin{spec}
    deCasteljau :: [NPoint] -> OverTime NPoint
    \end{spec}
que implementa o algoritmo respectivo.

\begin{enumerate}

\item Implemente |calcLine| como um catamorfismo de listas,
testando a sua definição com a propriedade:
    \begin{propriedade} Definição alternativa.
\begin{code}
prop_calcLine_def :: NPoint -> NPoint -> Float -> Bool
prop_calcLine_def p q d = calcLine p q d ==  zipWithM linear1d p q d
\end{code}
    \end{propriedade}

\item Implemente a função |deCasteljau| como um hilomorfismo, testando agora a propriedade:
    \begin{propriedade}
      Curvas de Bézier são simétricas.
\begin{code}
prop_bezier_sym :: [[Rational]] -> Gen Bool
prop_bezier_sym l = all (< delta) . calc_difs . bezs <$> elements ps  where
  calc_difs = (\(x, y) -> zipWith (\w v -> if w >= v then w - v else v - w) x y)
  bezs t    = (deCasteljau l t, deCasteljau (reverse l) (fromRational (1 - (toRational t))))
  delta = 1e-2
\end{code}
    \end{propriedade}

  \item Corra a função |runBezier| e aprecie o seu trabalho\footnote{%
        A representação em Gloss é uma adaptação de um
        \href{https://github.com/hrldcpr/Bezier.hs}{projeto}
        de Harold Cooper.} clicando na janela que é aberta (que contém, a verde, um ponto
        inicila) com o botão esquerdo do rato para adicionar mais pontos.
        A tecla |Delete| apaga o ponto mais recente.

\end{enumerate}

\Problema

Seja dada a fórmula que calcula a média de uma lista não vazia $x$,
\begin{equation}\label{eq:2}
avg\ x = \frac 1 k\sum_{i=1}^{k} x_i
\end{equation}
onde $k=length\ x$. Isto é, para sabermos a média de uma lista precisamos de dois catamorfismos: o que faz o somatório e o que calcula o comprimento a lista.
Contudo, é facil de ver que
\begin{quote}
	$avg\ [a]=a$
\\
	$avg (a:x) = \frac 1 {k+1}(a+\sum_{i=1}^{k} x_i) = \frac{a+k(avg\ x)}{k+1}$ para $k=length\ x$
\end{quote}
Logo $avg$ está em recursividade mútua com $length$ e o par de funções pode ser expresso por um único catamorfismo, significando que a lista apenas é percorrida uma vez.

\begin{enumerate}

\item	Recorra à lei de recursividade mútua para derivar a função
|avg_aux = cata (either b q)| tal que
|avg_aux = split avg length| em listas não vazias.

\item	Generalize o raciocínio anterior para o cálculo da média de todos os elementos de uma \LTree\ recorrendo a uma única travessia da árvore (i.e.\ catamorfismo).

\end{enumerate}
Verifique as suas funções testando a propriedade seguinte:
\begin{propriedade}
A média de uma lista não vazia e de uma \LTree\ com os mesmos elementos coincide,
a menos de um erro de 0.1 milésimas:
\begin{code}
prop_avg = nonempty .==>. diff .<=. const 0.000001 where
   diff l = avg l - (avgLTree . genLTree) l
   genLTree = anaLTree lsplit
   nonempty = (>[])
\end{code}
\end{propriedade}

\Problema	(\textbf{NB}: Esta questão é \textbf{opcional} e funciona como \textbf{valorização} apenas para os alunos que desejarem fazê-la.)

\vskip 1em \noindent
Existem muitas linguagens funcionais para além do \Haskell, que é a linguagem usada neste trabalho prático. Uma delas é o \Fsharp\ da Microsoft. Na directoria \verb!fsharp! encontram-se os módulos \Cp, \Nat\ e \LTree\ codificados em \Fsharp. O que se pede é a biblioteca \BTree\ escrita na mesma linguagem.

Modo de execução: o código que tiverem produzido nesta pergunta deve ser colocado entre o \verb!\begin{verbatim}! e o \verb!\end{verbatim}! da correspondente parte do anexo \ref{sec:resolucao}. Para além disso, os grupos podem demonstrar o código na oral.

\newpage

\part*{Anexos}

\appendix

\section{Como exprimir cálculos e diagramas em LaTeX/lhs2tex}
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

Os diagramas podem ser produzidos recorrendo à \emph{package} \LaTeX\
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

\section{Programação dinâmica por recursividade múltipla}\label{sec:recmul}
Neste anexo dão-se os detalhes da resolução do Exercício \ref{ex:exp} dos apontamentos da
disciplina\footnote{Cf.\ \cite{Ol18}, página \pageref{ex:exp}.},
onde se pretende implementar um ciclo que implemente
o cálculo da aproximação até |i=n| da função exponencial $exp\ x = e^x$,
via série de Taylor:
\begin{eqnarray}
	exp\ x
& = &
	\sum_{i=0}^{\infty} \frac {x^i} {i!}
\end{eqnarray}
Seja $e\ x\ n = \sum_{i=0}^{n} \frac {x^i} {i!}$ a função que dá essa aproximação.
É fácil de ver que |e x 0 = 1| e que $|e x (n+1)| = |e x n| + \frac {x^{n+1}} {(n+1)!}$.
Se definirmos $|h x n| = \frac {x^{n+1}} {(n+1)!}$ teremos |e x| e |h x| em recursividade
mútua. Se repetirmos o processo para |h x n| etc obteremos no total três funções nessa mesma
situação:
\begin{spec}
e x 0 = 1
e x (n+1) = h x n + e x n

h x 0 = x
h x (n+1) = x/(s n) * h x n

s 0 = 2
s (n+1) = 1 + s n
\end{spec}
Segundo a \emph{regra de algibeira} descrita na página \ref{pg:regra} deste enunciado,
ter-se-á, de imediato:
\begin{code}
e' x = prj . for loop init where
     init = (1,x,2)
     loop(e,h,s)=(h+e,x/s*h,1+s)
     prj(e,h,s) = e
\end{code}

\section{Código fornecido}\label{sec:codigo}

\subsection*{Problema 1}

\begin{code}
expd :: Floating a => a -> a
expd = Prelude.exp

type OutExpAr a = Either () (Either a (Either (BinOp, (ExpAr a, ExpAr a)) (UnOp, ExpAr a)))
\end{code}

\subsection*{Problema 2}
Definição da série de Catalan usando factoriais (\ref{eq:cat}):
\begin{code}
catdef n = div (fac((2*n))) ((fac((n+1))*(fac n)))
\end{code}
Oráculo para inspecção dos primeiros 26 números de Catalan\footnote{Fonte:
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
Função auxiliar:
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
Animação:
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
runBezier = play (InWindow "Bézier" (600, 600) (0,  0))
  black 50 initW picture actions tick

runBezierSym :: IO ()
runBezierSym = quickCheckWith (stdArgs {maxSize = 20, maxSuccess = 200} ) prop_bezier_sym
\end{code}

Compilação e execução dentro do interpretador:\footnote{Pode ser útil em testes
envolvendo \gloss{Gloss}. Nesse caso, o teste em causa deve fazer parte de uma função
|main|.}
\begin{code}
main = runBezier

run = do { system "ghc cp2021t" ; system "./cp2021t" }
\end{code}

\subsection*{QuickCheck}
Código para geração de testes:
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

\subsection*{Outras funções auxiliares}
%----------------- Outras definições auxiliares -------------------------------------------%
Lógicas:
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

\newpage

%----------------- Soluções dos alunos -----------------------------------------%

\section{Soluções dos alunos}\label{sec:resolucao}
Os alunos devem colocar neste anexo as suas soluções para os exercícios
propostos, de acordo com o "layout" que se fornece. Não podem ser
alterados os nomes ou tipos das funções dadas, mas pode ser adicionado
texto, disgramas e/ou outras funções auxiliares que sejam necessárias.

Valoriza-se a escrita de \emph{pouco} código que corresponda a soluções
simples e elegantes.

\subsection*{Funções dos alunos}

Redefinição polinomial de funções no capítulo 8 da biblioteca Cp, \textit{Basic functions, abbreviations}, que sofreram da \textbf{Restrição de Monomorsfismos}\footnote{Fonte: \href{https://wiki.haskell.org/Monomorphism_restriction}{HaskellWiki}.}:\\\\

\setlength{\leftskip}{1cm}
\setlength{\rightskip}{1cm}

\noindent{\huge\textbf{“}}

\setlength{\leftskip}{1.4cm}
\setlength{\rightskip}{1.4cm}

\noindent\textit{The "monomorphism restriction"\ is a counter-intuitive rule in Haskell type inference. If you forget to provide a type signature, sometimes this rule will fill the free type variables with specific types using "type defaulting"\ rules. The resulting type signature is always less polymorphic than you'd expect, so often this results in the compiler throwing type errors at you in situations where you expected it to infer a perfectly sane type for a polymorphic expression.}
\begin{flushright}{\huge\textbf{"\ \ \ \ \ \ \ }}\end{flushright}

\setlength{\leftskip}{0pt}
\setlength{\rightskip}{0pt}

\begin{code}
zeroP :: Num a => b -> a
zeroP = const 0

oneP :: Num a => b -> a
oneP = const 1

addP :: Num c => (c, c) -> c
addP = uncurry (+)

mulP :: Num c => (c, c) -> c
mulP = uncurry (*)
\end{code}

\subsection*{Problema 1} \label{pg:P1}
São dadas:
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

\newpage

%format (outExpAr) = "\mathsf{out}_{ExpAr}"
%format (recExpAr) = "\mathsf{F}_{ExpAr}"
%format (baseExpAr) = "\mathsf{B}_{ExpAr}"

\noindent Definir:

\begin{code}
outExpAr X             = i1 ()
outExpAr (N a)         = i2 $ i1 a
outExpAr (Bin op a b)  = i2 $ i2 $ i1 (op, (a, b))
outExpAr (Un op a)     = i2 $ i2 $ i2 (op, a)
---
recExpAr f = baseExpAr id id id f f id f
---
g_eval_exp v = either var (either num (either bin un)) where
    var  ()                 = v
    num  a                  = a
    bin  (Sum,     (a, b))  = a + b
    bin  (Product, (a, b))  = a * b
    un   (Negate, a)        = negate a
    un   (E,      a)        = expd a
---
eval_exp_int v = cataExpAr $ g_eval_exp_int v

g_eval_exp_int v = either var (either num (either bin un)) where
    var  ()                 = v
    num  a                  = a
    bin  (Sum,     (a, b))  = a + b
    bin  (Product, (0, b))  = 0
    bin  (Product, (a, 0))  = 0
    bin  (Product, (a, b))  = a * b
    un   (Negate, a)        = negate a
    un   (E,      0)        = 1
    un   (E,      a)        = expd a
---
clean (Bin Product (N 0) _)  = i2 $ i1 0
clean (Bin Product _ (N 0))  = i2 $ i1 0
clean (Un E (N 0))           = i2 $ i1 1
clean a = outExpAr a
---
gopt a = g_eval_exp a
\end{code}

\begin{code}
sd_gen :: Floating a =>
    Either () (Either a (Either (BinOp, ((ExpAr a, ExpAr a), (ExpAr a, ExpAr a))) (UnOp, (ExpAr a, ExpAr a))))
    -> (ExpAr a, ExpAr a)
sd_gen = either var (either num (either bin un)) where
  var _  = (X, N 1)
  num a  = (N a, N 0)
  bin  (Sum      , ((x, x'), (y, y')))  = (Bin  Sum      x y  , Bin  Sum x' y')
  bin  (Product  , ((x, x'), (y, y')))  = (Bin  Product  x y  , Bin  Sum (Bin Product x y') (Bin Product x' y))
  un   (Negate   ,  (x, x'))            = (Un   Negate   x    , Un   Negate x')
  un   (E        ,  (x, x'))            = (Un   E        x    , Bin  Product (Un E x) x')
\end{code}

\begin{code}
ad_gen v = either var (either num (either bin un)) where
  var _ = (v, 1)
  num a = (a, 0)
  bin  (Sum      , ((x, x'), (y, y')))  = (x + y     , x' + y')
  bin  (Product  , ((x, x'), (y, y')))  = (x * y     , x * y' + x' * y)
  un   (Negate   ,  (x, x'))            = (negate x  , negate x')
  un   (E        ,  (x, x'))            = (expd x    , expd x * x')
\end{code}

\newpage

\noindent\textbf{Prova da definição de outExpAr\\}

\begin{eqnarray*}
\xymatrix@@C=2cm{
  |ExpAr A| \ar@@/^2pc/[rr]^-{|outExpAr|} & {\cong} & |OutExpAr A| \ar@@/^2pc/[ll]^-{|inExpAr|}
}
\end{eqnarray*}

\begin{eqnarray*}
\start
	|outExpAr . inExpAr = id|
%
\just\equiv{ Def-inExpAr }
%
	|outExpAr . [const X, [N, [bin, uncurry Un]]] = id|
%
\just\equiv{ Fusão-+ }
%
	|[outExpAr . const X, outExpAr . [N, [bin, uncurry Un]]] = id|
%
\just\equiv{ Universal-+; Natural-id }
%
\begin{lcbr}
  |outExpAr . const X = i1|\\
  |outExpAr . [N, [bin, uncurry Un]] = i2|
\end{lcbr}
%
\just\equiv{ Fusão-+ }
%
\begin{lcbr}
  |outExpAr . const X = i1|\\\relax
  |[outExpAr . N, outExpAr . [bin, uncurry Un]] = i2|
\end{lcbr}
%
\just\equiv{ Universal-+; Natural-id }
%
\begin{lcbr}
  |outExpAr . const X = i1|\\
  \begin{lcbr}
    |outExpAr . N = i2 . i1|\\
    |outExpAr . [bin, uncurry Un] = i2 . i2|
  \end{lcbr}
\end{lcbr}
%
\just\equiv{ Fusão-+ }
%
\begin{lcbr}
  |outExpAr . const X = i1|\\
  \begin{lcbr}
    |outExpAr . N = i2 . i1|\\\relax
    |[outExpAr . bin, outExpAr . uncurry Un] = i2 . i2|
  \end{lcbr}
\end{lcbr}
%
\just\equiv{ Universal-+; Natural-id }
%
\begin{lcbr}
  |outExpAr . const X = i1|\\
  \begin{lcbr}
    |outExpAr . N = i2 . i1|\\
    \begin{lcbr}
      |outExpAr . bin = i2 . i2 . i1|\\
      |outExpAr . uncurry Un = i2 . i2 . i2|
    \end{lcbr}
  \end{lcbr}
\end{lcbr}
%
\just\equiv{ Igualdade extensional; Def-comp }
%
\begin{lcbr}
  |outExpAr ((const X ())) = i1 ()|\\
  \begin{lcbr}
    |outExpAr (N a) = i2 (i1 a)|\\
    \begin{lcbr}
      |outExpAr (bin (op, (a, b)))) = i2 (i2 (i1 (op, (a, b))))|\\
      |outExpAr ((uncurry Un (op, a))) = i2 (i2 (i2 (op, a)))|
    \end{lcbr}
  \end{lcbr}
\end{lcbr}
%
\just\equiv{ Def-const; Def-bin; Def-Un }
%
\begin{lcbr}
  |outExpAr X = i1 ()|\\
  \begin{lcbr}
    |outExpAr (N a) = i2 (i1 a)|\\
    \begin{lcbr}
      |outExpAr (Bin op a b) = i2 (i2 (i1 (op, (a, b))))|\\
      |outExpAr (Un op a) = i2 (i2 (i2 (op, a)))|
    \end{lcbr}
  \end{lcbr}
\end{lcbr}
\qed
\end{eqnarray*}

\newpage

\noindent\textbf{Prova da definição de g\_eval\_exp\\}

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |ExpAr A|
            \ar[d]_-{|eval_exp v|}
&
    |1 + (A + (BinOp >< (ExpAr A)|^2| + UnOp >< ExpAr A))|
            \ar[d]^{|id + (id + (id >< (eval_exp v >< eval_exp v) + id >< eval_exp v))|}
            \ar[l]_-{|inExpAr|}
\\
    |A|
&
    |1 + (A + (BinOp >< A|^2| + UnOp >< A))|
            \ar[l]^-{|g_eval_exp v|}
}
\end{eqnarray*}

%format g1 = "g_1"
%format g2 = "g_2"
%format g3 = "g_3"
%format g4 = "g_4"

\begin{eqnarray*}
\start
	|(eval_exp v) . inExpAr = g_eval_exp . fF (eval_exp v)|
%
\just\equiv{ Def-inExpAr; \ Def-F; \ ev v := eval\_exp v; \ g v := g\_eval\_exp v }
%
	|(ev v) . either (const X) (either N (either bin (uncurry Un))) = g . (id + (id + (id >< (ev v >< ev v) + id >< ev v)))|
%
\just\equiv{ Inferência do tipo de g }
%
	|(ev v) . either (const X) (either N (either bin (uncurry Un))) = either g1 (either g2 (either g3 g4)) . (id + (id + (id >< (ev v >< ev v) + id >< ev v)))|
%
\just\equiv{ 3 |><| Fusão-+; \ 3 |><| Asborsção-+; \ 2 |><| Natural-id }
%
    |either ((ev v) . (const X)) (either ((ev v) . N) (either ((ev v) . bin) ((ev v) . (uncurry Un)))) = either g1 (either g2 (either (g3 . (id >< (ev v >< ev v))) (g4 . (id >< ev v))))|
%
\just\equiv{ 3 |><| Eq-+; \ f = g $\equiv$ g = f }
%
\begin{lcbr}
  |g1 = (ev v) . (const X)|\\
  \begin{lcbr}
    |g2 = (ev v) . N|\\
    \begin{lcbr}
      |g3 . (id >< (ev v >< ev v)) = (ev v) . bin|\\
      |g4 . (id >< ev v) = (ev v) . (uncurry Un)|
    \end{lcbr}
  \end{lcbr}
\end{lcbr}
%
\just\equiv{ Igualdade extensional; \ Def-comp }
%
\begin{lcbr}
  |g1 () = ev v ((const X) ())|\\
  \begin{lcbr}
    |g2 a = ev v (N a)|\\
    \begin{lcbr}
      |g3 ((id >< (ev v >< ev v)) (binop, (a, b))) = ev v (bin (binop, (a, b)))|\\
      |g4 ((id >< ev v) (unop, a)) = ev v ((uncurry Un) (unop, a))|
    \end{lcbr}
  \end{lcbr}
\end{lcbr}
%
\just\equiv{ Def-const; \ Def-N; \ Def-bin; \ Def-|uncurry Un|; \ Def-|><| }
%
\begin{lcbr}
  |g1 () = ev v X|\\
  \begin{lcbr}
    |g2 a = ev v (N a)|\\
    \begin{lcbr}
      |g3 (binop, (ev v a, ev v b)) = ev v (Bin binop a b)|\\
      |g4 (unop, ev v a) = ev v (Un unop a)|
    \end{lcbr}
  \end{lcbr}
\end{lcbr}
%
\just\equiv{ Pattern matching em binop e unop }
%
\begin{lcbr}
  |g1 () = ev v X|\\
  \begin{lcbr}
    |g2 a = ev v (N a)|\\
    \begin{lcbr}
      \begin{lcbr}
        |g3 (Sum, (ev v a, ev v b)) = ev v (Bin Sum a b)|\\
        |g3 (Product, (ev v a, ev v b)) = ev v (Bin Product a b)|\\
      \end{lcbr}\\
      \begin{lcbr}
        |g4 (Negate, ev v a) = ev v (Un Negate a)|\\
        |g4 (E, ev v a) = ev v (Un E a)|
      \end{lcbr}
    \end{lcbr}
  \end{lcbr}
\end{lcbr}
%
\just\equiv{ Def-ev; \ |var| := |g1|; \ |num| := |g2|; \ |bin| := |g3|; \ |un| := |g4| }
%
\begin{lcbr}
  |var () = v|\\
  \begin{lcbr}
    |num a = a|\\
    \begin{lcbr}
      \begin{lcbr}
        |bin (Sum, (v1, v2)) = v1 + v2|\\
        |bin (Product, (v1, v2)) = v1 * v2|\\
      \end{lcbr}\\
      \begin{lcbr}
        |un (Negate, v1) = negate v1|\\
        |un (E, v1) = expd v1|
      \end{lcbr}
    \end{lcbr}
  \end{lcbr}
\end{lcbr}
\qed
\end{eqnarray*}

\newpage

\noindent\textbf{Propriedades usadas para definição de clean\\}

Elemento absovente da multiplicação:
\begin{eqnarray*}
    x * 0 & = & 0\\
    0 * x & = & 0
\end{eqnarray*}

Propriedade Expoente Zero:
\begin{eqnarray*}
    e ^ 0 & = & 1
\end{eqnarray*}
\\\\
\noindent\textbf{Provas das definições de sd\_gen e ad\_gen\\}

Devido à necessiade de conhecer não só as derivadas dos subtermos do produto e da exponenciação, mas também os seus valores originais de forma a fazer a sua derivação usámos um \textbf{Paramorfismo}\footnote{Fonte: \href{https://en.wikipedia.org/wiki/Paramorphism}{Wikipedia}.}. Algo que também é sugerido pelo \textit{wrapper}, $\pi_2$, das funções |sd| e |ad|.\\\\

\setlength{\leftskip}{1cm}
\setlength{\rightskip}{1cm}

\noindent{\huge\textbf{“}}

\setlength{\leftskip}{1.4cm}
\setlength{\rightskip}{1.4cm}

\textit{In formal methods of computer science, a paramorphism (from Greek $\pi\alpha\rho\acute{\alpha}$, meaning "close together") is an extension of the concept of catamorphism first introduced by Lambert Meertens to deal with a form which “eats its argument and keeps it too”.}

\textit{It is a more convenient version of catamorphism in that it gives the combining step function immediate access not only to the result value recursively computed from each recursive subobject, but the original subobject itself as well.}
\begin{flushright}{\huge\textbf{"\ \ \ \ \ \ \ }}\end{flushright}

\setlength{\leftskip}{0pt}
\setlength{\rightskip}{0pt}

Diagramas dos catamorfismos presentes em |sd| e |ad| respetivamente:

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |ExpAr A|
            \ar[d]_-{|split id sd|}
&
    |1 + (A + (BinOp >< (ExpAr A)|^2| + UnOp >< ExpAr A))|
            \ar[d]^{|id + (id + (id >< (split id sd >< split id sd) + id >< split id sd))|}
            \ar[l]_-{|inExpAr|}
\\
    |(ExpAr A)|^2
&
    |1 + (A + (BinOp >< ((ExpAr A)|^2| >< (ExpAr A)|^2|) + UnOp >< (ExpAr A)|^2|))|
            \ar[l]^-{|sd_gen|}
}
\end{eqnarray*}
\\
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |ExpAr A|
        \ar[d]_-{|split id (ad v)|}
&
    |1 + (A + (BinOp >< (ExpAr A)|^2| + UnOp >< ExpAr A))|
        \ar[d]^{|id + (id + (id >< (split id (ad v) >< split id (ad v)) + id >< split id (ad v)))|}
        \ar[l]_-{|inExpAr|}
\\
    {A}
&
    |1 + (A + (BinOp >< (A|^2| >< A|^2|) + UnOp >< A|^2|))|
        \ar[l]^-{|ad_gen v|}
}
\end{eqnarray*}

\newpage

\noindent Prova da definição de sd\_gen

\begin{eqnarray*}
\start
	|split id sd . inExpAr = sd_gen . fF (sd_gen)|
%
\just\equiv{ Def-inExpAr; \ Def-|fF| }
%
	|split id sd . either (const X) (either N (either bin (uncurry Un))) = sd_gen . (id + (id + (id >< split id sd|^2|) + id >< split id sd)))|
%
\just\equiv{ Inferência do tipo de g }
%
	|split id sd . either (const X) (either N (either bin (uncurry Un))) = either g1 (either g2 (either g3 g4)) . (id + (id + (id >< split id sd|^2|) + id >< split id sd)))|
%
\just\equiv{ 3 |><| Fusão-+; \ 3 |><| Asborsção-+; \ 2 |><| Natural-id }
%
    |either (split id sd . (const X)) (either (split id sd . N) (either (split id sd . bin) (split id sd . (uncurry Un))))| = [g_1, [g_2, [g_3 \cdot (|id >< split id sd|^2)), g_4 \cdot (|id >< split id sd|)]]]
%
\just\equiv{ 3 |><| Eq-+; \ f = g $\equiv$ g = f }
%
\begin{lcbr}
  |g1 = split id sd . (const X)|\\
  \begin{lcbr}
    |g2 = split id sd . N|\\
    \begin{lcbr}
      |g3 . (id >< split id sd|^2|) = split id sd . bin|\\
      |g4 . (id >< split id sd) = split id sd . (uncurry Un)|
    \end{lcbr}
  \end{lcbr}
\end{lcbr}
%
\just\equiv{ Igualdade extensional; \ Def-comp }
%
\begin{lcbr}
  |g1 () = split id sd ((const X) ())|\\
  \begin{lcbr}
    |g2 a = split id sd (N a)|\\
    \begin{lcbr}
      |g3 ((id >< (split id sd|^2|)) (binop, (a, b))) = split id sd (bin (binop, (a, b)))|\\
      |g4 ((id >< split id sd) (unop, a)) = split id sd ((uncurry Un) (unop, a))|
    \end{lcbr}
  \end{lcbr}
\end{lcbr}
%
\just\equiv{ Def-const; \ Def-N; \ Def-bin; \ Def-|uncurry Un|; \ Def-|><| }
%
\begin{lcbr}
  |g1 () = split id sd X|\\
  \begin{lcbr}
    |g2 a = split id sd (N a)|\\
    \begin{lcbr}
      |g3 (binop, (split id sd a, split id sd b)) = split id sd (Bin binop a b)|\\
      |g4 (unop, split id sd a) = split id sd (Un unop a)|
    \end{lcbr}
  \end{lcbr}
\end{lcbr}
%
\just\equiv{ Def-split; \ Natural-id }
%
\begin{lcbr}
  |g1 () = (X, sd X)|\\
  \begin{lcbr}
    |g2 a = (N a, sd (N a))|\\
    \begin{lcbr}
      |g3 (binop, ((a, sd a), (b, sd b))) = (Bin binop a b, sd (Bin binop a b))|\\
      |g4 (unop, (a, sd a)) = (Un unop a, sd (Un unop a))|
    \end{lcbr}
  \end{lcbr}
\end{lcbr}
%
\just\equiv{ Pattern matching em binop e unop }
%
\begin{lcbr}
  |g1 () = (X, sd X)|\\
  \begin{lcbr}
    |g2 a = (N a, sd (N a))|\\
    \begin{lcbr}
      \begin{lcbr}
        |g3 (Sum, ((a, sd a), (b, sd b))) = (Bin Sum a b, sd (Bin Sum a b))|\\
        |g3 (Product, ((a, sd a), (b, sd b))) = (Bin Product a b, sd (Bin Product a b))|\\
      \end{lcbr}\\
      \begin{lcbr}
        |g4 (Negate, (a, sd a)) = (Un Negate a, sd (Un Negate a))|\\
        |g4 (E, (a, sd a)) = (Un E a, sd (Un E a))|
      \end{lcbr}
    \end{lcbr}
  \end{lcbr}
\end{lcbr}
%
\just\equiv{ Def-sd; \ |var| := |g1|; \ |num| := |g2|; \ |bin| := |g3|; \ |un| := |g4| }
%
\begin{lcbr}
  |var () = (X, N 1)|\\
  \begin{lcbr}
    |num a = (N a, N 0)|\\
    \begin{lcbr}
      \begin{lcbr}
        |bin (Sum, ((a, a'), (b, b'))) = (Bin Sum a b, Bin Sum a' b')|\\
        |bin (Product, ((a, a'), (b, b'))) = (Bin Product a b, Bin Product a' b')|\\
      \end{lcbr}\\
      \begin{lcbr}
        |un (Negate, (a, a')) = (Un Negate a, Un Negate a')|\\
        |un (E, (a, a')) = (Un E a, Un E a')|
      \end{lcbr}
    \end{lcbr}
  \end{lcbr}
\end{lcbr}
\qed
\end{eqnarray*}

\newpage

\noindent Prova da definição de ad\_gen

\begin{eqnarray*}
\start
	|split id (ad v) . inExpAr = (ad_gen v) . fF (sd_gen)|
%
\just\equiv{ Def-inExpAr; \ Def-|fF| }
%
	|split id (ad v) . either (const X) (either N (either bin (uncurry Un))) = (ad_gen v) . (id + (id + (id >< split id (ad v)|^2|) + id >< split id (ad v))))|
%
\just\equiv{ Inferência do tipo de g }
%
	|split id (ad v) . either (const X) (either N (either bin (uncurry Un))) = either g1 (either g2 (either g3 g4)) . (id + (id + (id >< split id (ad v)|^2|) + id >< split id (ad v))))|
%
\just\equiv{ 3 |><| Fusão-+; \ 3 |><| Asborsção-+; \ 2 |><| Natural-id }
%
    |either (split id (ad v) . (const X)) (either (split id (ad v) . N) (either (split id (ad v) . bin) (split id (ad v) . (uncurry Un))))| = [g_1, [g_2, [g_3 \cdot (|id >< split id (ad v)|^2)), g_4 \cdot (|id >< split id (ad v)|)]]]
%
\just\equiv{ 3 |><| Eq-+; \ f = g $\equiv$ g = f }
%
\begin{lcbr}
  |g1 = split id (ad v) . (const X)|\\
  \begin{lcbr}
    |g2 = split id (ad v) . N|\\
    \begin{lcbr}
      |g3 . (id >< split id (ad v)|^2|) = split id (ad v) . bin|\\
      |g4 . (id >< split id (ad v)) = split id (ad v) . (uncurry Un)|
    \end{lcbr}
  \end{lcbr}
\end{lcbr}
%
\just\equiv{ Igualdade extensional; \ Def-comp }
%
\begin{lcbr}
  |g1 v = split id (ad v) ((const X) v)|\\
  \begin{lcbr}
    |g2 a = split id (ad v) (N a)|\\
    \begin{lcbr}
      |g3 ((id >< (split id (ad v)|^2|)) (binop, (a, b))) = split id (ad v) (bin (binop, (a, b)))|\\
      |g4 ((id >< split id (ad v)) (unop, a)) = split id (ad v) ((uncurry Un) (unop, a))|
    \end{lcbr}
  \end{lcbr}
\end{lcbr}
%
\just\equiv{ Def-const; \ Def-N; \ Def-bin; \ Def-|uncurry Un|; \ Def-|><| }
%
\begin{lcbr}
  |g1 v = split id (ad v) X|\\
  \begin{lcbr}
    |g2 a = split id (ad v) (N a)|\\
    \begin{lcbr}
      |g3 (binop, (split id (ad v) a, split id (ad v) b)) = split id (ad v) (Bin binop a b)|\\
      |g4 (unop, split id (ad v) a) = split id (ad v) (Un unop a)|
    \end{lcbr}
  \end{lcbr}
\end{lcbr}
%
\just\equiv{ Def-split; \ Natural-id }
%
\begin{lcbr}
  |g1 v = (X, (ad v) X)|\\
  \begin{lcbr}
    |g2 a = (N a, (ad v) (N a))|\\
    \begin{lcbr}
      |g3 (binop, ((a, (ad v) a), (b, (ad v) b))) = (Bin binop a b, (ad v) (Bin binop a b))|\\
      |g4 (unop, (a, (ad v) a)) = (Un unop a, (ad v) (Un unop a))|
    \end{lcbr}
  \end{lcbr}
\end{lcbr}
%
\just\equiv{ Pattern matching em binop e unop }
%
\begin{lcbr}
  |g1 v = (X, (ad v) X)|\\
  \begin{lcbr}
    |g2 a = (N a, (ad v) (N a))|\\
    \begin{lcbr}
      \begin{lcbr}
        |g3 (Sum, ((a, (ad v) a), (b, (ad v) b))) = (Bin Sum a b, (ad v) (Bin Sum a b))|\\
        |g3 (Product, ((a, (ad v) a), (b, (ad v) b))) = (Bin Product a b, (ad v) (Bin Product a b))|\\
      \end{lcbr}\\
      \begin{lcbr}
        |g4 (Negate, (a, (ad v) a)) = (Un Negate a, (ad v) (Un Negate a))|\\
        |g4 (E, (a, (ad v) a)) = (Un E a, (ad v) (Un E a))|
      \end{lcbr}
    \end{lcbr}
  \end{lcbr}
\end{lcbr}
%
\just\equiv{ Def-ad; \ |var| := |g1|; \ |num| := |g2|; \ |bin| := |g3|; \ |un| := |g4| }
%
\begin{lcbr}
  |var v = (v, 1)|\\
  \begin{lcbr}
    |num a = (a, 0)|\\
    \begin{lcbr}
      \begin{lcbr}
        |bin (Sum, ((a, a'), (b, b'))) = (a + b, a' + b')|\\
        |bin (Product, ((a, a'), (b, b'))) = (a * b, a * b' + a' * b)|\\
      \end{lcbr}\\
      \begin{lcbr}
        |un (Negate, (a, a')) = (negate a, negate a')|\\
        |un (E, (a, a')) = (expd a, expd a * a')|
      \end{lcbr}
    \end{lcbr}
  \end{lcbr}
\end{lcbr}
\qed
\end{eqnarray*}

\newpage

\noindent Testes de correção e performance:\\

Testes de performance de |optimize|\_|eval|:

\begin{code}
sums = cataNat (either (const (N 1)) (Bin Sum (N 3)))
p = Bin Product (sums 1000) (N 0)
\end{code}

\begin{verbatim}
*Main> eval_exp 1 p
0.0
(0.04 secs, 4,098,576 bytes)
*Main> eval_exp_int 1 p
0.0
(0.05 secs, 4,098,768 bytes)
*Main> optmize_eval 1 p
0.0
(0.02 secs, 368,704 bytes)
\end{verbatim}

\newpage

\subsection*{Problema 2}

%format def = "\mathbin{\stackrel{\mathrm{def}}{=}}"

Definir
\begin{code}
loop  (c,t,b)  = (div (t * c) b, 4 + t, 1 + b)
inic           = (1,2,2)         
prj   (c,_,_)  = c
\end{code}
por forma a que
\begin{code}
cat = prj . (for loop inic)
\end{code}
seja a função pretendida.
\textbf{NB}: usar divisão inteira.
Apresentar de seguida a justificação da solução encontrada.\\
\\
Fórmula que dá o n-ésimo número de Catalan:

\begin{eqnarray*}
    C_n = \frac {(2n)!} {(n+1)! (n!)}
\end{eqnarray*}
\\
Funções para recursividade mútua:

\begin{eqnarray*}
    c\ n & |def| & \frac {(2n)!} {(n+1)!(n!)}\\
    c\ 0 & = & 1\\
    c\ (n+1) & = & \frac {4n+2} {n+2} (c\ n)\\
\\
    t\ n & |def| & 4n + 2\\
    t\ 0 & = & 2\\
    t\ (n + 1) & = & 4 + t\ n\\
\\
    b\ n & |def| & n + 2\\
    b\ 0 & = & 2\\
    b\ (n + 1) & = & 1 + b\ n
\end{eqnarray*}
\\
Redefinindo c,

\begin{eqnarray*}
    c\ 0 & = & 1\\
    c\ (n+1) & = & \frac {t\ n} {b\ n} (c\ n)\\
             & = & \frac {(t\ n)(c\ n)} {b\ n}
\end{eqnarray*}

Das definições das funções |c|, |t| e |b| é usada a \emph{regra de algibeira} descrita na página \ref{pg:regra} deste enunciado para derivar uma implementação de C$_n$

\newpage

\noindent Desenvolvimento das expressões algébricas acima:

\begin{eqnarray*}
    c\ 0 & = & \frac {(2*0)!} {(0+1)!(0!)} = \frac {0!} {1! * 1} = \frac {1} {1} = 1\\
\\
    c\ (n+1) & = & \frac {(2(n+1))!} {((n+1)+1)!((n+1)!)}\\
             & = & \frac {(2n+2)!} {(n+2)!(n+1)!}\\
             & = & \frac {(2n+2)(2n+1)(2n)!} {(n+2)(n+1)!(n+1)n!}\\
             & = & \frac {(2n+2)(2n+1)} {(n+2)(n+1)} \cdot \frac {(2n)!} {(n+1)!n!}\\
             & = & \frac {4n+2} {n+2} (c\ n)\\
\\
    t\ 0 & = & 4 * 0 + 2 = 0 + 2 = 2\\
\\
    t\ (n + 1) & = & 4(n + 1) + 2\\
               & = & 4n + 4 + 2\\
               & = & 4 + (4n + 2)\\
               & = & 4 + t n\\
\\
    b\ 0 & = & 0 + 2 = 2\\
\\
    b\ (n + 1) & = & (n + 1) + 2\\
               & = & 1 + (n + 2)\\
               & = & 1 + b\ n\\
\end{eqnarray*}

\noindent Testes de correção e performance:

\begin{code}
oracleCmp = (map cat [0..25]) == oracle
catdefCmp = (map cat [0..99]) == (map catdef [0..99])
\end{code}

\begin{verbatim}
*Main> oracleCmp
True
*Main> catdefCmp
True
*Main> catdef 100000
1780545081823061907837573390658902019302...7404946049551384445058055232123705950784
(68.63 secs, 71,864,876,408 bytes)
*Main> cat 100000
1780545081823061907837573390658902019302...7404946049551384445058055232123705950784
(4.48 secs, 3,077,657,400 bytes)
\end{verbatim}

\newpage

\subsection*{Problema 3}

%format (inBezier) = "\mathsf{in}_{Bezier}"
%format (outBezier) = "\mathsf{out}_{Bezier}"
%format (hyloBezier (c) (a)) = "\llbracket\, " c, a "\,\rrbracket_{Bezier}"
%format (recBezier) = "\mathsf{F}_{Bezier}"
%format (baseBezier) = "\mathsf{B}_{Bezier}"

\begin{code}
calcLine :: NPoint -> (NPoint -> OverTime NPoint)
calcLine = cataList h where
    h = either f g
    f = const (const nil)
    g (d,f) l = case l of
        []     -> nil
        (x:xs) -> \z -> concat $ (sequenceA [singl . linear1d d x, f xs]) z
\end{code}
\begin{code}
deCasteljau :: [NPoint] -> OverTime NPoint
deCasteljau = hyloBezier conquer divide where
    divide   = (id -|- (id -|- split init tail)) . outBezier
    conquer  = either (const nil) (either const f)
    f (a,b)  = \pt -> (calcLine (a pt) (b pt)) pt
\end{code}
\begin{code}
outBezier []   = i1 ()
outBezier [a]  = i2 $ i1 a
outBezier l    = i2 $ i2 l
---
hyloBezier f g = f . recBezier (hyloBezier f g) . g 
---
recBezier f = id -|- (id -|- f >< f)
\end{code}

\newpage

%format (cataList (x)) = "\llparenthesis\, " x "\,\rrparenthesis"
%format (inList) = "\mathsf{in}_{List}"
%format (outList) = "\mathsf{out}_{List}"

\noindent\textbf{Prova da definição de calcLine}
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |NPoint|
           \ar[d]_-{|cataList h|}
           \ar[r]^-{|outList|}
&
    |1 + Rational + NPoint|
           \ar[d]^{|1 + id >< (cataList (h))|}
\\
    |(Overtime NPoint)|^{NPoint}
&
    |1 + Rational + (Overtime NPoint)|^{NPoint}
           \ar[l]^-{|h|}
}
\end{eqnarray*}

\begin{eqnarray*}
\start
    \begin{lcbr}
        |calcLine [] = const nil|\\
        |calcLine (p:x) = curry g p (calcLine x)|\\
    \end{lcbr}
%
\just\equiv{ Def-comp }
%
    \begin{lcbr}
        |calcLine . nil a = const (const nil) a|\\
        |calcLine . cons (p,x) = g . (id >< calcLine) (p,x)|\\
    \end{lcbr}
%
\just\equiv{ Igualdade extensional }
%
    \begin{lcbr}
        |calcLine . nil = const (const nil)|\\
        |calcLine . cons = g . (id >< calcLine)|\\
    \end{lcbr}
%
\just\equiv{ Eq-+; \ Natural-id }
%
    |either (calcLine . nil) (calcLine . cons) = either (const (const  nil)) (g . (id >< calcLine))|
%
\just\equiv{ Fusão-+; \ Absorção-+ }
%
    |calcLine . either nil cons = either (const (const nil)) g . (id + id >< calcLine))|
%
\just\equiv{ Def-inList; \ Def-|fF| }
%
    |calcLine . inList = either (const (const nil)) g . fF calcLine|
%
\just\equiv{ Universal-cata }
%
    |calcLine = cataList (either (const (const nil)) g)|
\qed
\end{eqnarray*}
\\
\indent Conclui-se assim que |h = either (cons (cons nil)) g| onde |g| é definido por:
\begin{spec}
   g (d,f) l = case l of
       []     -> nil
       (x:xs) -> \z -> concat $ (sequenceA [singl . linear1d d x, f xs]) z
\end{spec}

\newpage
\noindent\textbf{Prova da definição de deCasteljau}

\begin{eqnarray*}
\start
    \begin{lcbr}
        |deCasteljau [] = nil|\\
        |deCasteljau [p] = const p|\\
        |deCasteljau l = \pt -> (calcLine (p pt) (q pt)) pt|\\
    \end{lcbr}
%
\just\equiv{ p = deCasteljau (init l); \ q = deCasteljau (tail l) }
%
    \begin{lcbr}
        |deCasteljau [] = nil|\\
        |deCasteljau [p] = const p|\\
        |deCasteljau l = \pt -> (calcLine (deCasteljau (init l) pt) (deCasteljau (tail l) pt)) pt|\\
    \end{lcbr}
%
\just\equiv{ Igualdade extensional; Def-comp }
%
    \begin{lcbr}
        |deCasteljau . nil = const nil|\\
        |deCasteljau . singl =| const\\
        |deCasteljau = uncurry calcLine . deCasteljau|^2| . split init tail|\\
        %|deCasteljau = \pt -> (uncurry calcLine . deCasteljau|^2| . split init tail) pt|\\
    \end{lcbr}
%
\just\equiv{ 2 |><| Eq-+; \ 2 |><| Fusão-+; \ 2 |><| Absorção-+ }
%
    |deCasteljau . either nil (either singl id) = |[\underline{nil}, [const, |uncurry calcLine|]]| . (id + (id + deCasteljau|^2|)) . (id + (id + split init tail))| 
    %|deCasteljau . either nil (either singl id) = |[\underline{nil}, [const, (|\pt -> (uncurry calcLine . deCasteljau|^2)\ pt)]]|. (id + (id + split init tail))| 
%
\just\equiv{ Shunt-left }
%
    |deCasteljau = |[\underline{nil}, [const, |uncurry calcLine|]]| . (id + (id + deCasteljau|^2|)) . (id + (id + split init tail)) . outBezier| 
\qed
\end{eqnarray*}

Esta prova não é satisfatória para definir |deCasteljau| como um hylomorfismo devido à dificuldade de proceder nesta com a função anónima. Porém, seguindo esta prova e outros exemplos da aula 9 da disciplina é possivél concluir que:
\begin{itemize}
  \item |divide = (id + (id + split init tail)) . outBezier|
  \item |conquer = either (const nil) (either const f)|
  \item |recBezier f = id + (id + f >< f)|
\end{itemize}
Onde a função |f| em |conquer| é definida por:
\begin{itemize}
  \item |f (a,b) = \pt -> (calcLine (a pt) (b pt)) pt|
\end{itemize}

\newpage

\noindent\textbf{Testes de correção}\\

Definições das funções do Problema 3 dadas como especificações:

\begin{code}
calcLineSpec :: NPoint -> (NPoint -> OverTime NPoint)
calcLineSpec []     = const nil
calcLineSpec (p:x)  = curry g p (calcLineSpec x) where
   g :: (Rational, NPoint -> OverTime NPoint) -> (NPoint -> OverTime NPoint)
   g (d,f) l = case l of
       []     -> nil
       (x:xs) -> \z -> concat $ (sequenceA [singl . linear1d d x, f xs]) z
\end{code}

\begin{code}
deCasteljauSpec :: [NPoint] -> OverTime NPoint
deCasteljauSpec [] = nil
deCasteljauSpec [p] = const p
deCasteljauSpec l = \pt -> (calcLine (p pt) (q pt)) pt where
  p = deCasteljauSpec (init l)
  q = deCasteljauSpec (tail l)
\end{code}

Funções de verificação das funções definidas como resposta ao Problema 3 através das especificações destas:

\begin{code}
verifyCalcLine pt1 pt2 x = (calcLine pt1 pt2 x) == (calcLineSpec pt1 pt2 x)
verifyDeCasteljau pts x = (deCasteljau pts x) == (deCasteljauSpec pts x)
\end{code}

Verificação no ghci:

\begin{verbatim}
*Main> verifyCalcLine [0,0] [0,1] 0.5
True
*Main> verifyDeCasteljau [[0,0],[0,1],[1,0]] 0.5
True
*Main> map fromRational $ deCasteljau [[0,0],[0,1],[1,0]] 0.5
[0.25,0.5]
\end{verbatim}

\begin{figure}[h!]
  \centering
  \includegraphics[width=0.4\textwidth]{cp2021t_media/deCasteljau.png}
  \caption{Exemplo de curva de Bézier criada com as funções dadas como especificação.}
\end{figure}

\newpage

\subsection*{Problema 4}

Solução para listas não vazias:
\begin{code}
avg = p1 . avg_aux
\end{code}

%format (inNList) = "\mathsf{in}_{NList}"
%format (outNList) = "\mathsf{out}_{NList}"
%format (cataNList (x)) = "\llparenthesis\, " x "\,\rrparenthesis_{NList}"
%format (recNList) = "\mathsf{F}_{NList}"

%format a1 = "a_1"
%format a2 = "a_2"
%format b1 = "b_1"
%format b2 = "b_2"

\begin{code}
avg_aux = cataNList (either init loop) where
    loop  (a,(b,c))  = ((a + b * c) / (c + 1), c + 1)
    init  a          = (a, 1)
\end{code}
Solução para árvores de tipo \LTree:
\begin{code}
avgLTree = p1.cataLTree gene where
    gene = either init loop
    loop  ((a1,b1),(a2,b2))  = ((a1 * b1 + a2 * b2) / (b1 + b2), b1 + b2)
    init  a                  = (a, 1)
\end{code}
Definições de funções para catamorfismos sobre listas não vazias:
\begin{code}
inNList :: Either a (a, [a]) -> [a]
inNList = either singl cons
---
outNList :: [a] -> Either a (a, [a])
outNList [a]     = i1 a
outNList (a:as)  = i2 (a,as)
---
cataNList :: (Either a (a, b) -> b) -> [a] -> b
cataNList g = g . recNList (cataNList g) . outNList
---
recNList :: (a -> b) -> Either x (y, a) -> Either x (y, b)
recNList f = id -|- id >< f
\end{code}

\newpage

\noindent\textbf{Prova da definição de out$_{NList}$}

\begin{eqnarray*}
\xymatrix@@C=1.5cm{
  |A + A >< A|^+ \ar@@/^2pc/[rr]^-{|outNList|} & {\cong\ \ \ \ \ \ \ } & |A|^+ \ar@@/^2pc/[ll]^-{|inNList|}
}
\end{eqnarray*}

\begin{eqnarray*}
\start
    |outNList . inNList = id|
%
\just\equiv{ Def-|inNList| }
%
    |outNList . either singl cons = id|
%
\just\equiv{ Fusão-+ }
%
    |either (outNList . singl) (outNList . cons) = id|
%
\just\equiv{ Universal-+; \ Natural-id }
%
    \begin{lcbr}
        |outNList . singl = i1|\\
        |outNList . cons = i2|\\
    \end{lcbr}
%
\just\equiv{ Igualdade extensional; \ Def-comp }
%
    \begin{lcbr}
        |outNList (singl a) = i1 a|\\
        |outNList (cons (a, as)) = i2 (a, as)|\\
    \end{lcbr}
%
\just\equiv{ Def-singl; \ Def-cons }
%
    \begin{lcbr}
        |outNList [a] = i1 a|\\
        |outNList (a : as) = i2 (a, as)|\\
    \end{lcbr}
\qed
\end{eqnarray*}

\newpage

%format q1 = "q_1"
%format q2 = "q_2"

\noindent\textbf{Prova da definição do gene de avg\_aux}

\begin{eqnarray*}
\xymatrix@@C=2cm{
    {A^+}
            \ar[d]_-{|avg_aux|}
&
    {A + A |><| A^+}
            \ar[d]^{|id + id >< avg_aux|}
            \ar[l]_-{|inNList|}
\\
    A |><| \N^+
&
    {A + A |><| (A |><| \N^+)}
            \ar[l]^-{|[b,q]|}
}
\end{eqnarray*}

\begin{eqnarray*}
\start
	|avg_aux = cataNList (either b q)|
%
\just\equiv{ |avg_aux = split avg length| }
%
	|split avg length = cataNList (either b q)|
%
\just\equiv{ Inferência dos tipos de b e q }
%
	|split avg length = cataNList (either (split b1 b2) (split q1 q2))|
%
\just\equiv{ Lei da troca }
%
	|split avg length = cataNList (split (either b1 q1) (either b2 q2))|
%
\just\equiv{ Lei da recursividade mútua (Fokkinga) }
%
    \begin{lcbr}
        |avg . inNList = either b1 q1 . fF (split avg length)|\\
        |length . inNList = either b2 q2 . fF (split avg length)|\\
    \end{lcbr}
%
\just\equiv{ Def-inNList; \ Def-|fF| }
%
    \begin{lcbr}
        |avg . either singl cons = either b1 q1 . (id + id >< (split avg length))|\\
        |length . either singl cons = either b2 q2 . (id + id >< (split avg length))|\\
    \end{lcbr}
%
\just\equiv{ 2 |><| Fusão-+; \ 2 |><| Absorção-+; \ 2 |><| Natural-id }
%
    \begin{lcbr}
        |either (avg . singl) (avg . cons) = either b1 (q1 . (id >< (split avg length)))|\\
        |either (length . singl) (length . cons) = either b2 (q2 . (id >< (split avg length)))|\\
    \end{lcbr}
%
\just\equiv{ 2 |><| Eq-+; \ f = g |==| g = f }
%
    \begin{lcbr}
        \begin{lcbr}
            |b1 = avg . singl|\\
            |q1 . (id >< (split avg length)) = avg . cons|\\
        \end{lcbr}\\
        \begin{lcbr}
            |b2 = length . singl|\\
            |q2 . (id >< (split avg length)) = length . cons|\\
        \end{lcbr}
    \end{lcbr}
%
\just\equiv{ Igualdade extensional; \ Def-comp }
%
    \begin{lcbr}
        \begin{lcbr}
            |b1 a = avg (singl a)|\\
            |q1 ((id >< (split avg length)) (a, as)) = avg (cons (a, as))|\\
        \end{lcbr}\\
        \begin{lcbr}
            |b2 a = length (singl a)|\\
            |q2 ((id >< (split avg length)) (a, as)) = length (cons (a, as))|\\
        \end{lcbr}
    \end{lcbr}
%
\just\equiv{ Def-cons; \ Def-|><|; \ Def-split; \ Def-singl; \ Natural-id }
%
    \begin{lcbr}
        \begin{lcbr}
            |b1 a = avg [a]|\\
            |q1 (a, (avg as, length as)) = avg (a : as)|\\
        \end{lcbr}\\
        \begin{lcbr}
            |b2 a = length [a]|\\
            |q2 (a, (avg as, length as)) = length (a : as)|\\
        \end{lcbr}
    \end{lcbr}
%
\just\equiv{ Def-avg; \ Def-length }
%
    \begin{lcbr}
        \begin{lcbr}
            |b1 a = a|\\
            |q1 (a, (avg as, length as)) = (a + avg as * length as) / (legth as + 1)|\\
        \end{lcbr}\\
        \begin{lcbr}
            |b2 a = 1|\\
            |q2 (a, (avg as, length as)) = length as + 1|\\
        \end{lcbr}
    \end{lcbr}
\qed
\end{eqnarray*}

\newpage

\noindent\textbf{Prova da definição do gene de avgLTree}

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |LTree A|
            \ar[d]_-{|cataLTree (either b q)|}
&
    {A + (|LTree A|)^2}
            \ar[d]^{|id + cataLTree (either b q)|^2}
            \ar[l]_-{|inT|}
\\
    {A |><| \N^+}
&
    {A + (A |><| \N^+)^2}
            \ar[l]^-{|[b,q]|}
}
\end{eqnarray*}

\begin{eqnarray*}
\start
	|avgLTree = cataLTree (either b q)|
%
\just\equiv{ |avgLTree = split avg length| }
%
	|split avg length = cataLTree (either b q)|
%
\just\equiv{ Inferência dos tipos de b e q }
%
	|split avg length = cataLTree (either (split b1 b2) (split q1 q2))|
%
\just\equiv{ Lei da troca }
%
	|split avg length = cataLTree (split (either b1 q1) (either b2 q2))|
%
\just\equiv{ Lei da recursividade mútua (Fokkinga) }
%
    \begin{lcbr}
        |avg . inT = either b1 q1 . fF (split avg length)|\\
        |length . inT = either b2 q2 . fF (split avg length)|\\
    \end{lcbr}
%
\just\equiv{ Def-in; \ Def-|fF| }
%
    \begin{lcbr}
        |avg . either Leaf Fork = either b1 q1 . (id + (split avg length)|^2)\\
        |length . either Leaf Fork = either b2 q2 . (id + (split avg length)|^2)\\
    \end{lcbr}
%
\just\equiv{ 2 |><| Fusão-+; \ 2 |><| Absorção-+; \ 2 |><| Natural-id }
%
    \begin{lcbr}
        |either (avg . Leaf) (avg . Fork)| = [b1, |q1 . (split avg length)|^2]\\
        |either (length . Leaf) (length . Fork)| = [b2, |q2 . (split avg length)|^2]\\
    \end{lcbr}
%
\just\equiv{ 2 |><| Eq-+; \ f = g |==| g = f }
%
    \begin{lcbr}
        \begin{lcbr}
            |b1 = avg . Leaf|\\
            |q1 . (split avg length)|^2| = avg . Fork|\\
        \end{lcbr}\\
        \begin{lcbr}
            |b2 = length . Leaf|\\
            |q2 . (split avg length)|^2| = length . Fork|\\
        \end{lcbr}
    \end{lcbr}
%
\just\equiv{ Igualdade extensional; \ Def-comp }
%
    \begin{lcbr}
        \begin{lcbr}
            |b1 a = avg (Leaf a)|\\
            |q1 ((split avg length)|^2\ |((a1,b1),(a2,b2)))= avg (Fork ((a1,b1),(a2,b2)))|\\
        \end{lcbr}\\
        \begin{lcbr}
            |b2 a = length (Leaf a)|\\
            |q2 ((split avg length)|^2\ |((a1,b1),(a2,b2))) = length (Fork ((a1,b1),(a2,b2)))|\\
        \end{lcbr}
    \end{lcbr}
%
\just\equiv{ Def-Leaf; Def-Fork; \ Def-|><|; \ Def-split; \ Natural-id }
%
    \begin{lcbr}
        \begin{lcbr}
            |b1 a = avg (Leaf a)|\\
            |q1 ((avg (a1,b1),length (a1,b1)),(avg (a2,b2),length (a2,b2))) = avg (Fork ((a1,b1),(a2,b2)))|\\
        \end{lcbr}\\
        \begin{lcbr}
            |b2 a = length (Leaf a)|\\
            |q2 ((avg (a1,b1),length (a1,b1)),(avg (a2,b2),length (a2,b2))) = length (Fork ((a1,b1),(a2,b2)))|\\
        \end{lcbr}
    \end{lcbr}
%
\just\equiv{ Def-avg; \ Def-length }
%
    \begin{lcbr}
        \begin{lcbr}
            |b1 a = a|\\
            |q1 ((a1,b1), (a2,b2)) = (a1 * b1 + a2 * b2) / (b1 + b2)|\\
        \end{lcbr}\\
        \begin{lcbr}
            |b2 a = 1|\\
            |q2 ((a1,b1), (a2,b2)) = b1 + b2|\\
        \end{lcbr}
    \end{lcbr}
\qed
\end{eqnarray*}

\newpage

\noindent\textbf{Testes de correção}\\

Por \ref{eq:2} podemos definir uma função que cálcula a média aritmética de uma lista como:

\begin{code}
avgListDef :: (Fractional a, Num a) => [a] -> a
avgListDef = uncurry (/) . split sum (fromIntegral . length)
\end{code}

Uma função que cálcula a média aritmética de uma LTree pode ser definida como a função que cálcula a média de uma lista após converter a LTree para tal lista através da função |tips| definida em |Cp.hs|:

\begin{code}
avgLTreeDef :: (Fractional a, Num a) => LTree a -> a
avgLTreeDef = avgListDef . tips
\end{code}

Funções de verificação das funções definidas como resposta ao Problema 4 através das definições feitas acimas:

\begin{code}
verifyAvgList = (<= 0.000001) . (uncurry (-)) . split avgListDef avg

verifyAvgLTree = (<= 0.000001) . (uncurry (-)) . split avgLTreeDef avgLTree . genLTree where
    genLTree = anaLTree lsplit
\end{code}

Verificação no ghci:

\begin{verbatim}
*Main> verifyAvgList [1.0, 1.3 .. 100]
True
*Main> verifyAvgLTree [1.0, 1.3 .. 100]
True
\end{verbatim}

\newpage

\subsection*{Problema 5}
Inserir em baixo o código \Fsharp\ desenvolvido, entre \verb!\begin{verbatim}! e \verb!\end{verbatim}!:

\begin{verbatim}
module cp2021t 

open Cp
//import Data.List
//import Data.Monoid

// (1) Datatype definition -----------------------------------------------------

type BTree<'a> = Empty | Node of 'a * (BTree<'a> * BTree<'a>)


let inBTree x = (either (konst Empty) Node) x

let outBTree x =
    match x with
    | Empty  -> i1 ()
    | Node (a,(b1,b2)) -> i2 (a,(b1,b2))

// (2) Ana + cata + hylo -------------------------------------------------------

// recBTree g = id -|- (id >< (g >< g))

let baseBTree f g = id -|- (f >< (g >< g))

let recBTree g = baseBTree id g

let rec cataBTree g = g << (recBTree (cataBTree g)) << outBTree 

let rec anaBTree g = inBTree << (recBTree (anaBTree g) ) << g

let hyloBTree h g = cataBTree h << anaBTree g

// (3) Map ---------------------------------------------------------------------

//instance Functor BTree
//         where fmap f = cataBTree ( inBTree . baseBTree f id )
let fmap f = cataBTree ( inBTree << baseBTree f id )

// equivalent to:
//       where fmap f = anaBTree ( baseBTree f id . outBTree )

// (4) Examples ----------------------------------------------------------------

// (4.1) Inversion (mirror) ----------------------------------------------------

let invBTree x = cataBTree (inBTree << (id -|- (id >< swap))) x

// (4.2) Counting --------------------------------------------------------------

let countBTree x = cataBTree (either (konst 0) (succ << (uncurry (+)) << p2)) x

// (4.3) Serialization ---------------------------------------------------------

let insord x = 
        let join(x,(l,r))=l @ [x] @ r
        in either nil join x

let inordt x = cataBTree insord  x                 // in-order traversal

let preord x =
        let  f(x,(l,r)) = x :: l @ r
        in (either nil f) x

let preordt x = cataBTree preord x // pre-order traversal

let postordt x = 
        let f(x,(l,r)) = l @ r @ [x]
        in cataBTree (either nil f) x

// (4.4) Quicksort -------------------------------------------------------------

let menor x z = z < x

let rec part p x =
    match x with
    | [] -> ([],[])
    | (h::t) -> if p h then let (s,l) = part p t in (h::s,l) else let (s,l) = part p t in (s,h::l)


let qsep x =
    match x with
    | [] -> Left ()
    | (h::t) -> Right (h,(part (menor h) t))

let qSort  x = hyloBTree insord qsep x // the same as (cataBTree inord) . (anaBTree qsep)


(* pointwise versions:
qSort [] = []
qSort (h:t) = let (t1,t2) = part (<h) t
              in  qSort t1 ++ [h] ++ qSort t2

or, using list comprehensions:

qSort [] = []
qSort (h:t) = qSort [ a | a <- t , a < h ] ++ [h] ++ 
              qSort [ a | a <- t , a >= h ]

*)

// (4.5) Traces ----------------------------------------------------------------

let cons x z = x::z

let rec elem x l =
    match l with
    | [] -> false
    | (h::t) -> if x=h then true else elem x t

let rec union l ls =
    match ls with
    | [] -> l
    | (h::t) -> if elem h l then union l t else (union l t) @ [h]

let tunion (a,(l,r)) = union (List.map (cons a) l) (List.map (cons a) r) 

let traces x = cataBTree (either (konst [[]]) tunion) x


// (4.6) Towers of Hanoi -------------------------------------------------------

// pointwise:
// hanoi(d,0) = []
// hanoi(d,n+1) = (hanoi (not d,n)) ++ [(n,d)] ++ (hanoi (not d, n))

let present x = insord x // same as in qSort

let strategy (d,n) =
        match (d,n) with
        | (d,0) -> i1 ()
        | (d,n) -> i2 ((n-1,d),((not d,n-1),(not d,n-1))) 

let hanoi x = hyloBTree present strategy x

(*
    The Towers of Hanoi problem comes from a puzzle marketed in 1883
    by the French mathematician Édouard Lucas, under the pseudonym
    Claus. The puzzle is based on a legend according to which
    there is a temple, apparently in Bramah rather than in Hanoi as
    one might expect, where there are three giant poles fixed in the
    ground. On the first of these poles, at the time of the world's
    creation, God placed sixty four golden disks, each of different
    size, in decreasing order of size. The Bramin monks were given
    the task of moving the disks, one per day, from one pole to another
    subject to the rule that no disk may ever be above a smaller disk.
    The monks' task would be complete when they had succeeded in moving
    all the disks from the first of the poles to the second and, on
    the day that they completed their task the world would come to
    an end!
    
    There is a well­known inductive solution to the problem given
    by the pseudocode below. In this solution we make use of the fact
    that the given problem is symmetrical with respect to all three
    poles. Thus it is undesirable to name the individual poles. Instead
    we visualize the poles as being arranged in a circle; the problem
    is to move the tower of disks from one pole to the next pole in
    a specified direction around the circle. The code defines H n d
    to be a sequence of pairs (k,d') where n is the number of disks,
    k is a disk number and d and d' are directions. Disks are numbered
    from 0 onwards, disk 0 being the smallest. (Assigning number 0
    to the smallest rather than the largest disk has the advantage
    that the number of the disk that is moved on any day is independent
    of the total number of disks to be moved.) Directions are boolean
    values, true representing a clockwise movement and false an anti­clockwise
    movement. The pair (k,d') means move the disk numbered k from
    its current position in the direction d'. The semicolon operator
    concatenates sequences together, [] denotes an empty sequence
    and [x] is a sequence with exactly one element x. Taking the pairs
    in order from left to right, the complete sequence H n d prescribes
    how to move the n smallest disks one­by­one from one pole to the
    next pole in the direction d following the rule of never placing
    a larger disk on top of a smaller disk.
    
    H 0     d = [],
    H (n+1) d = H n ¬d ; [ (n, d) ] ; H n ¬d.
    
    (excerpt from R. Backhouse, M. Fokkinga / Information Processing
    Letters 77 (2001) 71--76)
   
   *)
// (5) Depth and balancing (using mutual recursion) --------------------------

let h (a,((b1,b2),(d1,d2))) = (b1 && b2 && abs(d1-d2)<=1,1+max d1 d2)

let f ((b1,d1),(b2,d2)) = ((b1,b2),(d1,d2))

let baldepth x = 
    let g = either (konst(true,1)) (h << (id><f))
    in cataBTree g x


let balBTree x = p1 (baldepth x)

let depthBTree x = p2 (baldepth x)

(*
-- (6) Going polytipic -------------------------------------------------------

-- natural transformation from base functor to monoid
tnat :: Monoid c => (a -> c) -> Either () (a,(c, c)) -> c
tnat f = either (const mempty) (theta . (f >< theta))
         where theta = uncurry mappend

-- monoid reduction 

monBTree f = cataBTree (tnat f)

-- alternative to (4.2) serialization ----------------------------------------

preordt' = monBTree singl

-- alternative to (4.1) counting ---------------------------------------------

countBTree' = monBTree (const (Sum 1))

-- (7) Zipper ----------------------------------------------------------------

data Deriv a = Dr Bool a (BTree a)

type Zipper a = [ Deriv a ]

plug :: Zipper a -> BTree a -> BTree a
plug [] t = t
plug ((Dr False a l):z) t = Node (a,(plug z t,l))
plug ((Dr True  a r):z) t = Node (a,(r,plug z t))

---------------------------- end of library ----------------------------------
*)

\end{verbatim}

\newpage

\subsection*{Outras soluções}

%format (cond a b c) = "{" a "} \rightarrow {" b "}, {" c "}"

\begin{code}
-- Definição point free de g\_eval\_exp
g_eval_exp_pf v = either (const v) (either id (either bin un)) where
    bin             = ap . (binop  >< id)
    un              = ap . (unop   >< id)
    binop  Sum      = addP
    binop  Product  = mulP
    unop   Negate   = negate
    unop   E        = expd
--
-- Definição point wise de g\_eval\_exp com condicionais
g_eval_exp_cpw v = either g1 (either g2 (either g3 g4)) where
    g1 () = v
    g2 a  = a
    g3 (binop, (a, b))  | binop == Sum  = a + b
                        | otherwise     = a * b
    g4 (unop, a)  | unop == Negate  = negate a 
                  | otherwise       = expd a
--
-- Definição point free de g\_eval\_exp com condicionais
g_eval_exp_cpf v = either g1 (either g2 (either g3 g4)) where
    g1 = const v
    g2 = id
    g3 = cond ((Sum ==) . p1) (addP . p2) (mulP . p2)
    g4 = cond ((Negate ==) . p1) (negate . p2) (expd . p2)
\end{code}

\begin{code}
-- Definição point free de sd\_gen
sd_gen_pf :: Floating a =>
    Either () (Either a (Either (BinOp, ((ExpAr a, ExpAr a), (ExpAr a, ExpAr a))) (UnOp, (ExpAr a, ExpAr a))))
    -> (ExpAr a, ExpAr a)
sd_gen_pf = either (const (X, N 1)) (either (split N (const (N 0))) (either bin un)) where
  bin  = ap . (binop  >< id)
  un   = ap . (unop   >< id)
  binop  Sum      = split (uncurry (Bin Sum) . (p1 >< p1)) (uncurry (Bin Sum) . (p2 >< p2))
  binop  Product  = split (uncurry (Bin Product) . (p1 >< p1)) (uncurry (Bin Sum) . split (uncurry (Bin Product) . (p1 >< p2)) (uncurry (Bin Product) . (p2 >< p1)))
  unop   Negate   = (Un Negate >< Un Negate)
  unop   E        = split (Un E . p1) (uncurry (Bin Product) . (Un E >< id))
\end{code}

\begin{code}
-- Definição point free de ad\_gen
ad_gen_pf v = either (const (v, 1)) (either (split id (const 0)) (either bin un)) where
  bin  = ap . (binop  >< id)
  un   = ap . (unop   >< id)
  binop  Sum      = split (addP . (p1 >< p1)) (addP . (p2 >< p2))
  binop  Product  = split (mulP . (p1 >< p1)) (addP . split (mulP . (p1 >< p2)) (mulP . (p2 >< p1)))
  unop   Negate   = (negate >< negate)
  unop   E        = split (expd . p1) (mulP . (expd >< id))
\end{code}

\begin{code}
-- Definição point free de avg\_aux
avg_aux_pf = cataNList (either (split id oneP) (split (uncurry (/) . split (addP . (id >< mulP)) (succ . p2 . p2)) (succ . p2 . p2)))
--
-- Definição point free de avgLTree
avgLTree_pf = p1 . cataLTree gene where
    gene = either (split id oneP) (split (uncurry (/) . split (addP . (mulP >< mulP)) (addP . (p2 >< p2))) (addP . (p2 >< p2)))
\end{code}

%----------------- Fim do anexo com soluções dos alunos ------------------------%

%----------------- Índice remissivo (exige makeindex) -------------------------%

\printindex

%----------------- Bibliografia (exige bibtex) --------------------------------%

\bibliographystyle{plain}
\bibliography{cp2021t}

%----------------- Fim do documento -------------------------------------------%
\end{document}
