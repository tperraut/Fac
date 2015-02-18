
public interface Transporteur <T extends Transportable>{
	
	/**
	 * Tentative d'ajout d'un élément au chargement de l'élément.
	 * @param t  l'objet transportable à ajouter au chargement.
	 * @return  true si l'ajout a eu lieu, et false sinon.
	 */
	public boolean ajouterTransportable(T t);
	
	/**
	 * Calcul du poids des choses transportées.
	 * @return  le poids total des choses transportées.
	 */	
	public int poidsDesTransportables();
	
}
