Require Coq.extraction.Extraction.
Require Coq.extraction.ExtrOcamlBasic.


Require Coq.extraction.ExtrOcamlNatInt.
Extract Inductive nat => int [ "0" "Stdlib.succ" ]
 "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Require Coq.extraction.ExtrOcamlNativeString.

Require MiniP4.Syntax.
Require MiniP4.Interp.

Cd "extraction".
Separate Extraction MiniP4.Syntax.
Separate Extraction MiniP4.Interp.
Cd "..".
