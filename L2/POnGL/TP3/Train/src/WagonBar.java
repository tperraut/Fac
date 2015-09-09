
public class WagonBar extends Wagon {

	/**
	 * Constructeur de WagonBar, pour lequel la capacité en passagers
	 * est fixée à 0.
	 * @param poids  indique le poids de l'élément à vide.
	 */
	public WagonBar(int poids)
	{
	    super(poids, 0);
	}
	
	/**
	 * Produit un descriptif de l'élément.
	 */
	public String toString(){
		return "WagonBar : poids = " + calculerPoids();
	}

}
