import { Component, OnInit } from '@angular/core';
import { UserServiceService } from '../../services/user-service/user-service.service';
import { MyRestaurantsService } from '../../services/my-restaurant/my-restaurants.service'
import { IYelpRestaurant } from '../../interfaces/yelp-restaurant-interface';
import { YelpRestaurant } from '../../models/yelp-restaurant';
import { Subscription } from 'rxjs';

@Component({
	selector: 'd-app-configurator',
	templateUrl: './d-app-configurator.component.html',
	styleUrls: ['./d-app-configurator.component.css']
})
export class DAppConfiguratorComponent implements OnInit {
	private currentMenuPage: number;
	private restaurantsPopulated: boolean;
	private hunger: boolean;
	private location: string;
	private price: string;
	private categories: string;
	private term: string
	private myRestaurantDataSubscription: Subscription;
	private mySavedRestaurants: IYelpRestaurant[];

	constructor(private configService: UserServiceService, private restaurantService: MyRestaurantsService) { 
	}

	ngOnInit() {
		this.currentMenuPage = 1;
		this.myRestaurantDataSubscription = this.restaurantService.restaurants
			.subscribe(restaurants => this.mySavedRestaurants = restaurants);
	}

	receivePreviousPageEvent() {
		this.decrementMenuPage();
	}

	receiveBackToStartEvent() {
		this.currentMenuPage = 1;
		this.configService.clearSearchQuery();
	}

	receiveHungerEvent($event) {
		this.hunger = $event;
		this.incrementMenuPage();
	}

	receiveLocationEvent($event) {
		this.location = $event;
		this.incrementMenuPage();
	}

	receiveTermEvent($event) {
		this.term = $event;
		this.incrementMenuPage();
	}

	receivePriceEvent($event) {
		this.price = $event;
		this.incrementMenuPage();
	}

	receiveCategoriesEvent($event) {
		this.categories = $event;
		this.incrementMenuPage();
	}

	incrementMenuPage() {
		this.currentMenuPage++;
	}

	decrementMenuPage() {
		this.currentMenuPage--;
	}

	populateRestaurants() {
		this.restaurantsPopulated = true;
	}

	combineAllQueries($event) {
		if($event) {
			this.configService.buildSearchQuery("term", this.term);
			this.configService.buildSearchQuery("location", this.location);
			this.configService.buildSearchQuery("price", this.price);
			this.configService.buildSearchQueryCategory(this.categories);
		}
	}
}
