import { Component, OnInit, Output, EventEmitter } from '@angular/core';
import { UserServiceService } from '../../services/user-service/user-service.service'
import { MyRestaurantsService } from '../../services/my-restaurant/my-restaurants.service'
import { HttpErrorResponse } from '@angular/common/http';
import { IYelpRestaurant } from '../../interfaces/yelp-restaurant-interface';
import { YelpRestaurant } from '../../models/yelp-restaurant';
import { Subscription } from 'rxjs';

@Component({
	selector: 'yelp-restaurant-list',
	templateUrl: './yelp-restaurant-list.component.html',
	styleUrls: ['./yelp-restaurant-list.component.css']
})
export class YelpRestaurantListComponent implements OnInit {
	@Output() backToStartValue = new EventEmitter<boolean>();
	@Output() combineQueryValue = new EventEmitter<boolean>();
	private listOfRestaurants: IYelpRestaurant[] = [];
	private myListOfRestaurants: IYelpRestaurant[] = [];
	private numberOfRestaurants: number;
	private jsonResult: JSON;
	private restaurantsPopulated: boolean;
	private myRestaurantDataSubscription: Subscription;

	constructor(private configService: UserServiceService, private restaurantService: MyRestaurantsService) { }

	ngOnInit() {
		this.myRestaurantDataSubscription = this.restaurantService.restaurants
			.subscribe(incomingRestaurantList => this.myListOfRestaurants = incomingRestaurantList);
	}

	emitBackResponse() {
		this.backToStartValue.emit(false);
		this.configService.clearSearchQuery;
	}

	combineQueryResponse() {
		this.combineQueryValue.emit(true);
		this.sendRestaurantRequest();
	}

	sendRestaurantRequest() {
		this.configService.retrieveRestaurants().subscribe(data => {
			this.jsonResult = data['businesses'];
			this.numberOfRestaurants = Object.keys(this.jsonResult).length;
			this.parseJsonResult();
		},
			(err: HttpErrorResponse) => {
				console.log(err.message);
			}
		);
	}

	AddAll() {
		let incomingRestaurants: IYelpRestaurant[] = this.listOfRestaurants.filter(rst => rst.added);
		incomingRestaurants.forEach(rest => {
			this.restaurantService.addRestaurant(rest);
		});
		this.restaurantService.updateRestaurants();
	}

	clearAll() {
		this.restaurantService.clearAllRestaurants();
	}

	parseJsonResult() {
		this.listOfRestaurants = [];
		for (let i = 0; i < this.numberOfRestaurants; i++) {
			let restaurant = new YelpRestaurant();

			//easy setters
			restaurant.imageUrl = this.jsonResult[i]['image_url'];
			restaurant.url = this.jsonResult[i]['url'];
			restaurant.name = this.jsonResult[i]['name'];
			restaurant.id = this.jsonResult[i]['id'];
			restaurant.phone = this.jsonResult[i]['phone'];
			restaurant.price = this.jsonResult[i]['price'];
			restaurant.rating = this.jsonResult[i]['rating'];
			restaurant.reviewCount = this.jsonResult[i]['review_count'];

			//address
			let address1 = this.jsonResult[i]['location']['address1']
			let city = this.jsonResult[i]['location']['city']
			let state = this.jsonResult[i]['location']['state']
			let zipCode = this.jsonResult[i]['location']['zip_code']
			let country = this.jsonResult[i]['location']['country']
			let finalAddress = `${address1}, ${city}, ${state} ${zipCode}, ${country}`
			restaurant.address = finalAddress;

			//categories
			let numberOfCategories = Object.keys(this.jsonResult[i]['categories']).length;
			let allCategories = [];
			for (let j = 0; j < numberOfCategories; j++) {
				let category = this.jsonResult[i].categories[j].title;
				allCategories.push(category);
			}
			restaurant.categories = allCategories;

			//add to list
			this.listOfRestaurants.push(restaurant);
		}
		this.restaurantsPopulated = true;
	}

	printAllRestaurants() {
		for (let i = 0; i < 3; i++) {
			let categories = "";
			for (let j = 0; j < this.listOfRestaurants[i].categories.length; j++) {
				if (j + 1 === this.listOfRestaurants[i].categories.length) {
					categories += this.listOfRestaurants[i].categories[j];
					break;
				}
				categories += this.listOfRestaurants[i].categories[j] + ", ";

			}

			console.log(this.listOfRestaurants[i].name)
			console.log(this.listOfRestaurants[i].id)
			console.log(this.listOfRestaurants[i].address)
			console.log(categories);
			console.log(this.listOfRestaurants[i].phone)
			console.log(this.listOfRestaurants[i].price)
			console.log(this.listOfRestaurants[i].rating)
			console.log(this.listOfRestaurants[i].reviewCount)
			console.log(this.listOfRestaurants[i].imageUrl)
			console.log('--------------------------------------------------------------')
		}
	}
}
