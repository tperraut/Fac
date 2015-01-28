import java.lang.Integer;
import java.lang.String;

// Un module pour les couleurs
import java.awt.Color;
// Trois modules pour l'interface graphique
import IG.ZoneCliquable;
import IG.Grille;
import IG.Fenetre;


/*

   Classe principale NReines.
   Ici on initialise le jeu et l'affichage.

   Pour l'affichage, on fait appel à la classe [IG.Fenetre],
   et on utilise deux méthodes de cette classe dont les
   signatures sont :

   public void ajouteElement([composant graphique]);
   public void dessineFenetre();

*/

public class NReines
{
	public static void main(String[] args)
	{
		// Création d'une fenêtre graphique, d'un échiquiers
		// et de deux boutons.
		Fenetre fenetre = new Fenetre("N reines");
		Plateau plateau = new Plateau(Integer.parseInt(args[0]));
		Validation validation = new Validation(plateau);
		Indice indice = new Indice(plateau);
		// On précise que l'échiquier et les boutons doivent
		// être affichés dans la fenêtre graphique.
		fenetre.ajouteElement(plateau);
		fenetre.ajouteElement(validation);
		fenetre.ajouteElement(indice);
		fenetre.dessineFenetre();
	}
}

/*

   Bouton de validation. On ne demande à ce bouton de ne réagir
   qu'aux clics gauches. Le bouton doit se colorer en vert si
   la configuration actuelle du plateau est licite, et en rouge
   sinon.

   Les deux appels de méthode suivants permettent respectivement
   de colorer le bouton en vert ou rouge :

   setBackground(Color.GREEN);
   setBackground(Color.RED);

   On fait appel à la classe abstraite [IG.ZoneCliquable].
   Pour cela, il faut définir deux méthodes correspondant aux
   actions à effectuer lors d'un clic avec le bouton gauche ou
   avec le bouton droit. Leurs signatures sont :

   public void clicGauche();
   public void clicDroit();

*/

class Validation extends ZoneCliquable
{
	private Plateau plateau;

	public Validation(Plateau plateau)
	{
		// Création d'une zone cliquable de dimensions 80*25 pixels,
		// et contenant le texte "Valider".
		super("Valider", 80, 25);
		this.plateau = plateau;
	}

	public void clicGauche()
	{
		if (this.plateau.verifieConfiguration())
			setBackground(Color.GREEN);
		else
			setBackground(Color.RED);
	}
	public void clicDroit() {}
}

/*

   Bouton de demande d'indice. On ne demande à ce bouton de ne
   réagir qu'aux clics gauches. Si la configuration actuelle du
   plateau peut être complétée en une configuration complète,
   alors le bouton doit se colorer en vert, et doit indiquer un
   prochain coup possible en colorant la case correspondante en
   bleu.

*/

class Indice extends ZoneCliquable
{
	private Plateau plateau;

	public Indice(Plateau plateau)
	{
		// Création d'une zone cliquable de dimensions 80*25 pixels,
		// et contenant le texte "Indice".
		super("Indice", 80, 25);
		this.plateau = plateau;
	}

	public void clicGauche() { /* À compléter */ }
	public void clicDroit() {}
}



/*

   Une classe pour l'échiquier.

   La mention [extends Grille] permet d'afficher les cases
   sous la forme d'une grille, en utilisant la classe [IG.Grille].

   Lorsqu'une case [c] est créée, pour l'intégrer à l'affichage
   graphique il faut réaliser l'appel de méthode suivante :

   this.ajouteElement(c);

*/

class Plateau extends Grille
{
	// Attributs statiques
	private static int taille;
	private Case[][] tab;
	// Constructeur
	public Plateau(int taille)
	{
		// Initialisation de la grille graphique de dimensions 8*8
		super(taille, taille);
		this.taille = taille;
		this.tab = new Case[taille][taille];
		for (int i = 0; i < taille; i++)
		{
			for (int j = 0; j < taille; j++)
			{
				this.tab[i][j] = new Case(this);
				this.ajouteElement(this.tab[i][j]);
			}
		}
	}

	// Méthode de vérification générale.
	private int compteLigne(Case[] l)
	{
		int	nb;

		nb = 0;
		for (Case c : l)
		{
			if (!c.isempty())
				nb++;
		}
		return (nb);
	}
	private boolean verifieLignes()
	{
		for(Case[] l : this.tab)
		{
			if(compteLigne(l) > 1)
				return (false);
		}
		return (true);
	}
	private boolean verifieColumns()
	{
		int	nb;

		for (int i = 0; i < this.taille; i++)
		{
			nb = 0;
			for (Case[] l : this.tab)
			{
				if (!l[i].isempty())
					nb++;
				if (nb > 1)
					return (false);
			}
		}
		return (true);
	}
	//Left to Right
	private boolean verifieDiagLtR()
	{
		int	nb;

		//Diagonale de dessous
		for (int i = 0; i < this.taille; i++)
		{
			nb = 0;
			for (int j = 0; j < this.taille - i; j++)
			{
				if (!this.tab[i + j][j].isempty())
				nb++;
				if (nb > 1)
				return (false);
			}
		}
		//Diagonale de dessus
		for (int j = 1; j < this.taille; j++)
		{
			nb = 0;
			for (int i = 0; i < this.taille - j; i++)
			{
				if (!this.tab[i][i + j].isempty())
				nb++;
				if (nb > 1)
				return (false);
			}
		}
		return (true);
	}
	//Right to Left
	private boolean verifieDiagRtL()
	{
		int	nb;

		//Diagonale de dessous
		for (int i = 0; i < this.taille; i++)
		{
			nb = 0;
			for (int j = this.taille - 1; j >= i; j--)
			{
				if (!this.tab[this.taille - 1 + i - j][j].isempty())
				nb++;
				if (nb > 1)
				return (false);
			}
		}
		//Diagonale de dessus
		for (int i = 0; i < this.taille - 1; i++)
		{
			nb = 0;
			for (int j = this.taille - 2 - i; j >= 0; j--)
			{
				if (!this.tab[this.taille - 2 - i - j][j].isempty())
				nb++;
				if (nb > 1)
				return (false);
			}
		}
		return (true);
	}

	// Méthode vérifiant que la configuration actuelle est
	// résoluble et plaçant le cas échéant dans [indiceL] et
	// [indiceR] les coordonnées d'un coup possible vers une
	// solution.
	// La méthode est récursive, et explore tous les coups valides.
	// Lors de l'exploration d'un coup, la méthode modifie l'échiquier,
	// puis annule ses modifications lors du "backtrack".
	public boolean verifieResolubilite()
	{
		/* À remplacer ! */
		return false;
	}
	public boolean verifieConfiguration()
	{
		return (verifieLignes()
				&& verifieColumns()
				&& verifieDiagLtR()
				&& verifieDiagRtL());
	}
}

/*

   Une classe pour les cases du terrain de jeu.

   On demande à ces cases de réagir aux clics gauches.
   Lorsque l'on clique sur une case libre (blanche), celle-ci doit
   être colorée en noir et indiquée comme occupée.
   Lorsque l'on clique sur une case occupée (noire), celle-ci doit
   être colorée en blanc et indiquée comme libre.

   La mention [extends ZoneCliquable] permet de faire réagir les
   cases aux clics de souris, en utilisant [IG.ZoneCliquable] et
   les méthodes

   public void clicGauche();
   public void clicDroit();

*/

class Case extends ZoneCliquable
{
	private boolean	empty;
	// Constructeur
	public Case(Plateau plateau)
	{
		// Initialisation d'une case cliquable, de dimensions 40*40 pixels.
		super(40, 40);
		this.empty = true;
	}
	public boolean isempty()
	{
		return (this.empty);
	}
	// Action à effectuer lors d'un clic gauche.
	public void clicGauche()
	{
		if (this.empty)
			setBackground(Color.BLACK);
		if (!this.empty)
			setBackground(Color.WHITE);
		this.empty = !this.empty;
		/* À compléter */
	}

	// Action à effectuer lors d'un clic droit.
	public void clicDroit() { }

}
