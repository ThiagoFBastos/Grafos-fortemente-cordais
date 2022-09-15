codigo = forte
all: 
	g++ -std=c++17 -o $(codigo) $(codigo).cpp -O2 -Wall 
clean:
	rm $(codigo)
