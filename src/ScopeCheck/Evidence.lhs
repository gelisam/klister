\documentclass{article}
\title{Scope Checking Klister}
\usepackage{amsmath}
\usepackage{mathtools}
\usepackage{latexsym}
\usepackage{fancyvrb}
\usepackage[utf8]{inputenc}
\newenvironment{code}{\VerbatimEnvironment\begin{Verbatim}}{\end{Verbatim}}

% optionally automatically resized paired delimiters
\makeatletter % https://goo.gl/osSmHV
\DeclarePairedDelimiterX{\Braces}[1]{\{}{\}}{#1}
\DeclarePairedDelimiterX{\Brackets}[1]{[}{]}{#1}
\DeclarePairedDelimiterX{\Paren}[1]{\lparen}{\rparen}{#1}
\def\braces{\@ifstar{\Braces}{\Braces*}}
\def\brackets{\@ifstar{\Brackets}{\Brackets*}}
\def\paren{\@ifstar{\Paren}{\Paren*}}
\makeatother

% judgments
\newcommand{\ctx}[1]{#1\textbf{ ctx}}
\newcommand{\pat}[3]{#1 \vdash #2 \textbf{ pat} \leadsto #3}
\newcommand{\wellscoped}[2]{#1 \vdash #2\textbf{ well-scoped}}
\newcommand{\expandscope}[3]{#1 \vdash #2 \leadsto #3}

% patterns
\newcommand{\patIdent}[1]{\texttt{ident}\;#1}
\newcommand{\patVec}[1]{\texttt{vec}\;\brackets{#1}}
\newcommand{\patCons}[2]{\texttt{cons}\;\brackets{#1\;#2}}
\newcommand{\patEmpty}{\texttt{empty}}

% expressions
\newcommand{\eLam}[2]{\lambda #1.\;#2}
\newcommand{\eApp}[2]{#1\;#2}
\newcommand{\eAppII}[3]{\eApp{\eApp{#1}{#2}}{#3}}
\newcommand{\eAppIII}[4]{\eApp{\eApp{\eApp{#1}{#2}}{#3}}{#4}}
\newcommand{\ePure}[1]{\eApp{\texttt{pure}}{#1}}
\newcommand{\eBind}[2]{\eAppII{\texttt{bind}}{#1}{#2}}
\newcommand{\eError}[1]{\eApp{\texttt{error}}{#1}}
\newcommand{\eSend}[1]{\eApp{\texttt{send}}{#1}}
\newcommand{\eWait}[1]{\eApp{\texttt{wait}}{#1}}
% TODO: bound-identifier=?, free-identifier=?
\newcommand{\eSyntax}[1]{\eApp{\texttt{stx}}{#1}}
\newcommand{\eSyntaxCase}[2]{\texttt{syntax-case}\; #1\; #2}
\newcommand{\eIdentifier}[1]{#1}
\newcommand{\eTrue}{\texttt{true}}
\newcommand{\eFalse}{\texttt{false}}
\newcommand{\eSignal}[1]{\eApp{\texttt{signal}}{#1}} % TODO: ???
\newcommand{\eIf}[3]{\eAppIII{\texttt{if}}{#1}{#2}{#3}}
\newcommand{\eIdent}[1]{\eApp{\texttt{ident-syntax}}{#1}}
\newcommand{\eEmpty}{\texttt{empty-syntax}}
\newcommand{\eCons}[2]{\eAppII{\texttt{cons-syntax}}{#1}{#2}}
\newcommand{\eVec}[1]{\eAppII{\texttt{vec-syntax}}{#1}}

\newcommand{\hypspace}{\qquad} % space between hypotheses
\setlength{\jot}{1em} % space between equations in multi-line envs
\begin{document}
\section{Forms of Judgment}

\subsection{Well-formed contexts}

During scope checking, a context $\Gamma$ records the set of variables that are
in scope. Well-formed contexts are either empty ($\cdot$), or a context extended
with a variable.
\begin{gather*}
  \frac{}{\ctx{\cdot}} \\
  \frac{\ctx{\Gamma} \hypspace x\notin\Gamma}{\ctx{\Gamma , x}}
\end{gather*}
The remainder of rules presented here presuppose that all contexts are
well-formed.

\subsection{Patterns}

Patterns may add variables to the context. The pattern $\patIdent{x}$ matches an
identifier $x$ and makes it available on the RHS of the match:
\begin{equation*}
  \frac{}{\pat{\Gamma}{\patIdent{x}}{\Gamma,x}}
\end{equation*}
The pattern $\patVec{x_1\;\ldots\;x_n}$ matches a vector of syntax objects of
length $n$:
\begin{equation*}
  \frac{}{\pat{\Gamma}{\patVec{x_1\;\ldots\;x_n}}{\Gamma,x_1,\ldots,x_n}}
\end{equation*}
The pattern $\patCons{x}{y}$ matches a cons cell of syntax objects:
\begin{equation*}
  \frac{}{\pat{\Gamma}{\patCons{x}{y}}{\Gamma,x,y}}
\end{equation*}
The empty pattern $\patEmpty$ matches an empty list of syntax objects, and binds
no new variables in the context:
\begin{equation*}
  \frac{}{\pat{\Gamma}{\patEmpty}{\Gamma}}
\end{equation*}

\subsection{Well-scoped expressions}


Variables are well-scoped in environments that contain them:
\begin{equation*}
  \frac{x \in \Gamma}{\wellscoped{\Gamma}{x}}
\end{equation*}
% TODO(lb): Can lambdas bind variables from elsewhere in the context (not just the end)?
Lambda expressions extend the context with an additional variable:
\begin{equation*}
  \frac{\wellscoped{\Gamma,x}{e}}{\wellscoped{\Gamma}{\eLam{x}{e}}}
\end{equation*}
A \texttt{syntax-case} expression is well-scoped in $\Gamma$ when the RHS of
each branch is well-scoped in $\Gamma$ extended with the variables bound
in the pattern in the LHS of that branch:
\begin{equation*}
  \frac{
  \wellscoped{\Gamma}{e_0}
  \hypspace \pat{\Gamma}{p_i}{\Gamma_i}
  \hypspace \wellscoped{\Gamma_i}{e_i}
  }{\wellscoped{\Gamma}{\eSyntaxCase{e_0}{\brackets{p_i\;e_i}}}}
\end{equation*}

All other expressions are well-scoped when their subtrees are:
\begin{gather*}
  \frac{
    \wellscoped{\Gamma}{e_0}
    \hypspace \wellscoped{\Gamma}{e_1}
  }{\wellscoped{\Gamma}{\eApp1{e_0}{e_1}}} \\
  \frac{\wellscoped{\Gamma}{e}}{\wellscoped{\Gamma}{\ePure{e}}} \\
  \frac{
    \wellscoped{\Gamma}{e_0}
    \hypspace \wellscoped{\Gamma}{e_1}
  }{\wellscoped{\Gamma}{\eBind{e_0}{e_1}}} \\
\end{gather*}

\begin{code}
module ScopeCheck.Evidence
  (
  ) where

data Evidence = Evidence ()
\end{code}

\end{document}
