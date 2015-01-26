
public class	JMine
{
	public static void main(String[] arg)
	{
		Terrain terrain = new Terrain(4, 6, 0,7);
	}
}

class	Terrrain
{
	private int			hauteur;
	private int			largeur;
	public boolean[][]	tab;

	public Terrain(int hauteur, int largeur, double densite)
	{
		this.hauteur = hauteur;
		this.largeur = largeur;
		this.densite = densite;
		this.tab = new boolean[hauteur][largeur];
		for(boolean[] ligne : this.tab)
		{
			for(int j = 0; j < largeur; j++)
			{
				//return 0 if math.random < 0,2 else 1
				ligne[j] = Math.random() < densite;
			}
		}
		private boolean	coordonnees_legales(int x, int y)
		{
			return (x <= 0 & x >)
		}
		public int	compte_voisines(int x, int y)
		{
			est_piegee(x - 1, y - 1);
		}
	}
}

class	Case
{
	boolean	piegee;
	boolean	vue;

	public	Case(boolean b)
	{
		this.piegee = b;
		this.vue = false;

	}

	public void	clicDroit()
	{
		if (this.piegee)
		{
			setBackground(Color.RED);
		}
		else
		{
			nb = terrain.compte_voisines(this.x, this.y);
		}
	}
}
