import { async, ComponentFixture, TestBed } from '@angular/core/testing';

import { YelpRestaurantListComponent } from './yelp-restaurant-list.component';

describe('YelpRestaurantListComponent', () => {
	let component: YelpRestaurantListComponent;
	let fixture: ComponentFixture<YelpRestaurantListComponent>;

	beforeEach(async(() => {
		TestBed.configureTestingModule({
			declarations: [YelpRestaurantListComponent]
		})
			.compileComponents();
	}));

	beforeEach(() => {
		fixture = TestBed.createComponent(YelpRestaurantListComponent);
		component = fixture.componentInstance;
		fixture.detectChanges();
	});

	it('should create', () => {
		expect(component).toBeTruthy();
	});
});
