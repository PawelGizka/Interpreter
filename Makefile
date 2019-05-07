all:
	ghc Main.hs -o interpreter parser/AbsMy.hs parser/ErrM.hs parser/LexMy.hs parser/ParMy.hs parser/PrintMy.hs parser/SkelMy.hs

clean:
	-rm -f *.hi *.o parser/*.hi parser/*.o
