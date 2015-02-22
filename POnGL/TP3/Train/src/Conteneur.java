public class Conteneur implements Transportable {
	/**
	 * Un conteneur est caractérisé par son volume et son poids.
	 * Le volume détermine la place prise dans un porte-conteneur, à
	 * comparer avec la capacité du porte-conteneur, tandis que le poids
	 * est à comparer avec la capacité de traction des éléments moteurs.
	 */
	private final int volume;
	private final int poids;
	
	public Conteneur(int poids, int volume)
	{
		this.poids = poids;
		this.volume = volume;
	}
	
	/**
	 * Renvoie le poids du conteneur.
	 */
	@Override
	public int getPoids()
	{
		return (this.poids);
	}
	
	/**
	 * Renvoie le volume du conteneur.
	 */
	public int getVolume()
	{
		return (this.volume);
	}
	
	/**
	 * Produit un descriptif de l'élément.
	 */
	public String toString()
	{
		return ("conteneur de volume : " + String.valueOf(volume)
			+ " et de poids : " + String.valueOf(poids));
	}
}
