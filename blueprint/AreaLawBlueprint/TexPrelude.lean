import VersoBlueprint

/-! The paper's math macros (`paper/main.tex`, preamble), for the blueprint's KaTeX. -/

tex_prelude r#"
\def\Tr{\operatorname{Tr}}
\def\id{\operatorname{id}}
\def\supp{\operatorname{supp}}
\def\dist{\operatorname{dist}}
\def\diam{\operatorname{diam}}
\def\Sym{\operatorname{Sym}}
\def\poly{\operatorname{poly}}
\def\E{\mathbb E}
\def\R{\mathbb R}
\def\C{\mathbb C}
\def\Z{\mathbb Z}
\def\N{\mathbb N}
\def\ket#1{\lvert #1\rangle}
\def\bra#1{\langle #1\rvert}
\def\norm#1{\lVert #1\rVert}
"#
