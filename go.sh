bison parse.y -d
flex lex.l
gcc parse.tab.c -o main
#./main
