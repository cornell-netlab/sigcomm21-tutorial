Require Coq.extraction.Extraction.
Require Coq.extraction.ExtrOcamlBasic.


Require Coq.extraction.ExtrOcamlNatInt.
Extract Inductive nat => int [ "0" "Stdlib.succ" ]
 "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Require Coq.extraction.ExtrOcamlNativeString.

Require MiniP4.Syntax.
Require MiniP4.Interp.
Require MiniP4.Examples.ACL.
Require MiniP4.Examples.IPv4.
Extract Inlined Constant MiniP4.Interp.hash => "(fun x -> x)".

Cd "extraction".
Separate Extraction Syntax Interp ACL.
Cd "..".
