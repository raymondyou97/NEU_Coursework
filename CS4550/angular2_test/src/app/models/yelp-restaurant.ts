import { IYelpRestaurant } from "../interfaces/yelp-restaurant-interface"

export class YelpRestaurant implements IYelpRestaurant {
    name: string;
    id: string;
    rating: number;
    reviewCount: number;
    address: string;
    price: string;
    phone: string;
    categories: string[];
    url: string;
    imageUrl: string;
    added: boolean;

    constructor() {
        this.name = "";
        this.id = "";
        this.rating = 0;
        this.reviewCount = 0;
        this.address = "";
        this.price = "";
        this.phone = "";
        this.categories = [];
        this.url = "";
        this.imageUrl = "";
        this.added = false;
    }
}
