export interface IYelpRestaurant {
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
}
