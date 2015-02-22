public class Voiture implements Transportable
{
	private final int poids;
	private final char categorie;

	public Voiture(int poids, char categorie)
	{
		this.poids = poids;
		this.categorie = categorie;
	}
	@Override
	public int getPoids()
	{
		return (this.poids);
	}
	public int getCategorie()
	{
		return (this.categorie);
	}

}
