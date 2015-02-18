
public class Wagon extends EltTransporteur<Passager> {

	/**
	 * Constructeur de Wagon
	 * @param poids  indique le poids de l'élément à vide.
	 * @param capacite  indique le nombre de passagers que l'élément
	 * peut accueillir.
	 */
	private int placesRestantes;

	public Wagon(int poids, int capacite)
	{
		super(poids, capacite);
		this.placesRestantes = capacite;
	}

	/**
	 * Nombre de places encore disponibles dans le wagon.
	 */
	public int placesRestantes()
	{
		return (placesRestantes);
	}

	/**
	 * Retourne un descriptif du wagon et de son chargement.
	 */
	public String toString(){
		return "Wagon : poids total = " + getPoids() +
			", places occupées/capacité = " + cargo.size() + "/" + capacite +
			", passagers : " + cargoToString();
	}


}
