import { Injectable } from '@angular/core';
import { BehaviorSubject, Observable } from 'rxjs';
import { IYelpRestaurant } from '../../interfaces/yelp-restaurant-interface';

@Injectable({
	providedIn: 'root'
})
export class MyRestaurantsService {
	private dataSource: BehaviorSubject<IYelpRestaurant[]> = new BehaviorSubject<IYelpRestaurant[]>(null);
	private allRestaurants: IYelpRestaurant[] = [];

	get restaurants(): Observable<IYelpRestaurant[]> {
        return new Observable((fn: any) => this.dataSource.subscribe(fn));
	}
	
	constructor() { }

	getCurrentListOfMyRestaurants() {
		return this.allRestaurants;
	}
	
	updateRestaurants() {
		this.allRestaurants = Array.from(new Set(this.allRestaurants));
		this.dataSource.next(this.allRestaurants);
	}

	addRestaurant(restaurant: IYelpRestaurant) {
		this.allRestaurants.push(restaurant);
	}
	clearAllRestaurants() {
		this.allRestaurants = [];
		this.dataSource.next(this.allRestaurants)
	}
}
