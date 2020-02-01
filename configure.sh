rm -f _CoqProject
echo '-R . zfc'    > _CoqProject
echo axiom/*.v     >> _CoqProject
echo operation/*.v >> _CoqProject
echo relation/*.v  >> _CoqProject
coq_makefile -f _CoqProject -o Makefile
make
make gallinahtml
