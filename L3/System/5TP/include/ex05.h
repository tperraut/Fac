#ifndef EX05_H
# define EX05_H
# define SIZE 10
int	*creer_tableau(int n);
int	*allouer_tableau(int dim, int val);
void	afficher_tableau(int *t, int size);
void	liberer_tableau(int *t);
int	*recuperer_n_entiers(int n);
int	*recuperer_entiers(int n, int t_max);
int	**allouer_matrice(int li, int co, int val);
void	liberer_matrice(int **mat, int n);
void	afficher_matrice(int **mat, int li, int co);
#endif
