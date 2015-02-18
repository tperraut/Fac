
public class Autorail extends EltTransporteur<Passager> implements EltMoteur {
	
	/**
	 * La capacité de traction maximale de l'autorail.
	 */
	private int tractionMax;
	private int placesRestantes;
	/**
	 * Constructeur d'Autorail.
	 * @param poids  donne le poids de l'élément à vide.
	 * @param capacite  donne le nombre de passagers pouvant être transportés.
	 * @param tractionMax  donne la capacité de traction maximale.
	 */
	public Autorail(int poids, int capacite, int tractionMax) {
		super(poids, capacite);
		this.placesRestantes = capacite;
		this.tractionMax = tractionMax;
	}

	/**
	 * Renvoie la capacité de traction maximale de l'élément.
	 */
	@Override
	public int getTractionMax() {
		return (tractionMax);
	}
	
	/**
	 * Renvoie le nombre de places encore disponibles.
	 */
	public int placesRestantes(){
		return (placesRestantes);
	}
}
