public class Voiture extends EltTransporteur<Passager> implements Transportable
{
	private final int volume;

	public Voiture(int poids, int capacite, int volume)
	{
		super(poids, capacite);
		this.volume = volume;
	}
	public int getVolume()
	{
		return (this.volume);
	}
	public String toString()
	{
		return ("Voiture : Poids totale = " + this.getPoids() +
				", places occupees/capacite = " + cargo.size() + "/" + capacite +
				", volume = " + this.volume +
				", passagers = " + cargoToString());
	}
}
