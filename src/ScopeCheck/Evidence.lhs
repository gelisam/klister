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
\newcommand{\patCons}[2]{\texttt{cons}\;\brackets{#1,#2}}
\newcommand{\patEmpty}{\texttt{empty}}

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
  \frac{\ctx{\Gamma} \quad x\notin\Gamma}{\ctx{\Gamma , x}}
\end{gather*}
The remainder of rules presented here presuppose that all contexts are
well-formed.

\subsection{Patterns}

Patterns may add variables to the context. The pattern $\patIdent{x}$ matches an
identifier $x$ and makes it available on the RHS of the match:
\begin{equation*}
  \frac{}{\pat{\Gamma}{\patIdent{x}}{\Gamma,x}}
\end{equation*}
The pattern $\patVec{x_1,\ldots,x_n}$ matches a vector of syntax objects of
length $n$:
\begin{equation*}
  \frac{}{\pat{\Gamma}{\patVec{x_1,\ldots,x_n}}{\Gamma,x_1,\ldots,x_n}}
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

\begin{align*}
  \frac{
  \wellscoped{\Gamma}{e_0}
  \hypspace \pat{\Gamma}{p_i}{\Gamma_i}
  \hypspace \wellscoped{\Gamma_i}{e_i}
  }{\wellscoped{\Gamma}{\text{syntax-case } e_0 (\brackets{p_i e_i})}}
\end{align*}

\begin{align*}
  \frac{x \in \Gamma}{\wellscoped{\Gamma}{x}} \\
\end{align*}

\begin{code}
module ScopeCheck.Evidence
  (
  ) where

data Evidence = Evidence ()
\end{code}

\end{document}
