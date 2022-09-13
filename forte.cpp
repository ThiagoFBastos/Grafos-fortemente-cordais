#include <iostream>
#include <cstdlib>
#include <fstream>
#include <vector>
#include <utility>
#include <algorithm>
#include <queue>
#include <functional>
#include <set>

using namespace std;

vector<int> busca_lexicografica(vector<vector<int>>& G) {
	int n = G.size();

	vector<bool> marked(n, false);
	vector<int> order(n), id(n, 0), pos(n), ptr(1, n - 1);
	vector<vector<int>> R(n);
	vector<int> S;
	
	for(int i = 0; i < n; ++i) order[i] = pos[i] = i;

	for(int j = n; j; --j) {
		
		int v = order.back();
	
		--ptr[id[v]];
		order.pop_back();

		marked[v] = true;

		unordered_map<int, vector<int>> upd;

		for(int u : G[v]) {
			if(marked[u]) continue;
			upd[id[u]].push_back(u);
		}

		for(auto& [k, s] : upd) {
			ptr.push_back(ptr[k]);
			for(int u : s) {
				id[u] = (int)ptr.size() - 1;
				swap(order[pos[u]], order[ptr[k]]);
				swap(pos[u], pos[order[pos[u]]]);
				--ptr[k];
			}
		}

		S.push_back(v);
	}

	reverse(S.begin(), S.end());

	return S;
}

bool eh_subsequencia(vector<int>& A, vector<int>& B) {
	int i = 0;
	vector<int> a = A, b = B;
	sort(a.begin(), a.end());	
	a.resize(unique(a.begin(), a.end()) - a.begin());
	sort(b.begin(), b.end());
	for(int v : a) {
		while(i < (int)b.size() && v != b[i]) ++i;
		if(i == (int)b.size()) return false;
	}
	return true;
}

bool eh_eeps(vector<vector<int>>& G, vector<int>& eeps) {
	int n = G.size();

	vector<vector<int>> L(n), A(n);

	vector<int> pos(n);

	for(int i = 0; i < n; ++i) pos[eeps[i]] = i;

	for(int i = 0; i < n; ++i) {
		int v = eeps[i];

		vector<pair<int, int>> right;

		for(int u : G[v]) right.emplace_back(pos[u], u);

		sort(right.begin(), right.end());

		for(auto [k, u] : right) if(k > i) A[v].push_back(u);
	}

	for(int v : eeps) {
		if(!eh_subsequencia(L[v], A[v]))
			return false;

		for(int i = 1; i < (int)A[v].size(); ++i) 	
			L[A[v][0]].push_back(A[v][i]);
	}

	return true;
}

vector<vector<int>> MakeSets(vector<vector<int>>& G, vector<int>& eeps) {
	int n = G.size();

	vector<vector<int>> zeta;
	vector<int> deg(n, 0);
	vector<bool> existe(n, true);
	
	for(int v = 0; v < n; ++v) deg[v] = G[v].size();

	for(int i = 0; i < n; ++i) {
		int v = eeps[i];

		if(!existe[v]) continue;
	
		vector<int> S {v};
		
		for(int u : G[v]) {
			if(existe[u] && deg[u] == deg[v])
				S.push_back(u);
		}

		for(int u : S) {
			existe[u] = false;
			for(int w : G[u]) --deg[w];
		}

		zeta.push_back(S);
	}

	return zeta;
}

vector<int> SimpleToStrong(vector<vector<int>>& G, vector<vector<int>>& zeta) {
	int n = G.size(), cur_set = zeta.size();

	vector<int> wichSet(n), eeps, sz(n, 0), lastUpd(n, -1), nxt(n, -1);
	vector<vector<int>> S(n);

	for(int v = 0; v < n; ++v) G[v].push_back(v);

	for(int i = 0; i < (int)zeta.size(); ++i) {	
		nxt[i] = i != (int)zeta.size() - 1 ? i + 1 : -1;
		
		sz[i] = zeta[i].size();

		for(int v : zeta[i]) {
			wichSet[v] = i;
			eeps.push_back(v);
		}
	}

	for(int i = n - 1; i >= 0; --i) {
		int v = eeps[i];

		vector<int> sets;

		for(int u : G[v]) {
			int id = wichSet[u];
			if(lastUpd[id] != i) {
				lastUpd[id] = i;
				S[id] = {u};
				sets.push_back(wichSet[u]);
			} else 
				S[id].push_back(u);
		}

		for(int k : sets) {
			if((int)S[k].size() != sz[k]) {
				int last_nxt = nxt[k];
		
				nxt[k] = cur_set;
				nxt[cur_set] = last_nxt;

				sz[k] -= S[k].size();
				sz[cur_set] = S[k].size();
	
				for(int u : S[k]) wichSet[u] = cur_set;

				++cur_set;
			}	
		}	
	}

	for(int v = 0; v < n; ++v) G[v].pop_back();

	vector<int> eepf;

	for(auto& v : S) v.clear();

	for(int u = 0; u < n; ++u) S[wichSet[u]].push_back(u);

	for(int k = 0; k != -1; k = nxt[k])
		for(int u : S[k])
			eepf.push_back(u);

	return eepf;
}

bool eh_eepf_muito_simples(vector<vector<int>>& G, vector<int>& eepf) {
	int n = G.size();		
	vector<vector<int>> A(n);

	vector<int> pos(n);

	for(int i = 0; i < n; ++i) pos[eepf[i]] = i;

	for(int i = n - 1; i >= 0; --i) {
		int v = eepf[i];

		for(int u : G[v]) {
			if(pos[u] < pos[v]) continue;
			A[u].push_back(v);
			A[v].push_back(u);
		}

		sort(A[v].begin(), A[v].end(), [&pos](int u, int v) {
			return pos[u] < pos[v];
		});		


		for(int j = 0; j < (int)A[v].size() - 1; ++j) {
			int v1 = A[v][j], v2 = A[v][j + 1];
			A[v1].push_back(v1); A[v2].push_back(v2);
			if(!eh_subsequencia(A[v1], A[v2])) 
				return false;
			A[v1].pop_back(); A[v2].pop_back();
		}
	}

	return true;
}

int main(int argc, char* argv[]) {

	if(argc != 2) {
		cout << "use: ./forte f\n";
		cout << "f é o arquivo com o grafo que tem o template:\n";
		cout << "n: o número de vértices\n";
		cout << "m: o número de arestas\n";
		cout << "u v: o par de vértices por linha indexado em [1, n]\n";
		return 0;
	}

	fstream fs(argv[1], ios_base :: in);
	
	int n, m;

	fs >> n >> m;
	
	vector<vector<int>> G(n);

	for(int i = 0; i < m; ++i) {
		int u, v;
		fs >> u >> v;
		--u, --v;
		G[u].push_back(v);
		G[v].push_back(u);
	}

	auto eeps = busca_lexicografica(G);
/*
	cout << "eeps\n";
	for(int u : eeps) cout << u + 1 << ' ';
	cout << '\n';
*/
	if(!eh_eeps(G, eeps)) {
		cout << "Parece que o grafo não é cordal\n";
		return 0;
	}

	cout << "Parece que o grafo é cordal\n";

	auto zeta = MakeSets(G, eeps);
/*
	cout << "zeta\n";
	for(auto& S : zeta) {
		for(int u:S) cout<<u+1<<' ';
		cout<<'\n';
	}
*/
	auto eepf = SimpleToStrong(G, zeta);
/*
	cout << "eepf\n";
	for(int v : eepf) cout << v + 1 << ' ';
	cout << '\n';*/

	if(eh_eepf_muito_simples(G, eepf)) cout << "Parece que é fortemente cordal\n";
	else cout << "Parece que não é fortemente cordal\n";

	return 0;
}
