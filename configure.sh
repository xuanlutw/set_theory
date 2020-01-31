rm -f _CoqProject
echo '-R . zfc' > _CoqProject
echo *.v >> _CoqProject
coq_makefile -f _CoqProject -o Makefile
make
make gallinahtml
