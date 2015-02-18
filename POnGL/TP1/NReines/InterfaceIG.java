/*******************************************************/
/*  Mode d'emploi pour la mini-interface graphique IG  */
/*******************************************************/


/* Classe d'une fenêtre dans laquelle on peut insérer
   des éléments graphiques.
   Voir IG/Fenetre.java
   */

interface Fenetre
{

	// Création
	public Fenetre (String nom);

	// Ajout d'un élément graphique
	public void ajouteElement (JComponent element);

	// Affichage de la fenêtre
	public void dessineFenetre();

}

/* Classe permettant d'aligner des éléments graphiques
   sur une grille.
   Voir IG/Grille.java
   */

interface Grille
{
	// Création
	public Grille (int hauteur, int largeur);

	// Ajout d'éléments dans la grille
	public void ajouteElement(JComponent element);

}

/* Classe d'un élément graphique sur lequel on peut
   cliquer pour déclencher des actions.
   Voir IG/ZoneCliquable.java
   */

interface ZoneCliquable
{
	// Création d'une zone cliquable, avec ou sans texte.
	public ZoneCliquable(int x, int y);
	public ZoneCliquable(String texte, int x, int y);

	// Actions à effectuer lors des clics.
	public abstract void clicGauche();
	public abstract void clicDroit();

	// Modification de l'étiquette.
	public void changeTexte(String texte);
}

