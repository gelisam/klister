\documentclass{article}
\title{Scope Checking Klister}
\usepackage{amsmath}
\usepackage{latexsym}
\usepackage{fancyvrb}
\usepackage[utf8]{inputenc}
\newenvironment{code}{\VerbatimEnvironment\begin{Verbatim}}{\end{Verbatim}}
\newcommand{\ctx}[1]{#1\textbf{ ctx}}
\newcommand{\pat}[3]{#1 \vdash #2 \textbf{ pat} \leadsto #3}
\newcommand{\wellscoped}[2]{#1 \vdash #2\textbf{ well-scoped}}
\newcommand{\expandscope}[3]{#1 \vdash #2 \leadsto #3}
\begin{document}
\section{Forms of Judgment}

\subsection{Well-formed contexts}
\begin{align*}
  \frac{}{\ctx{\cdot}} \\
  \frac{\ctx{\Gamma} \quad x\notin\Gamma}{\ctx{\Gamma , x}}
\end{align*}

Presupposition throughout that all contexts are well-formed

\subsection{Well-formed patterns}

\subsection{Well-scoped expressions}

\begin{align*}
  \frac{
  \wellscoped{\Gamma}{e_0} 
  \quad \pat{\Gamma}{p_i}{\Gamma_i}
  \quad \wellscoped{\Gamma_i}{e_i}
  }{\wellscoped{\Gamma}{\text{syntax-case } e_0 ([p_i e_i])}}
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
