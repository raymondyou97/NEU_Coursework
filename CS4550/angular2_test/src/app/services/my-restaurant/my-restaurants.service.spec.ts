import { TestBed } from '@angular/core/testing';

import { MyRestaurantsService } from './my-restaurants.service';

describe('MyRestaurantsService', () => {
  beforeEach(() => TestBed.configureTestingModule({}));

  it('should be created', () => {
    const service: MyRestaurantsService = TestBed.get(MyRestaurantsService);
    expect(service).toBeTruthy();
  });
});
